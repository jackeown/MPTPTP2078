%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0276+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:02 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   36 (  57 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   47 ( 106 expanded)
%              Number of equality atoms :   18 (  54 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k4_xboole_0(k2_tarski(A,B),C) != k1_xboole_0
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(A)
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(B)
          & k4_xboole_0(k2_tarski(A,B),C) != k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_179,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_xboole_0(k2_tarski(A_47,B_48),C_49) = k1_xboole_0
      | ~ r2_hidden(B_48,C_49)
      | ~ r2_hidden(A_47,C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_241,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_30])).

tff(c_315,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_243,plain,(
    ! [B_50,C_51,A_52] :
      ( ~ r2_hidden(B_50,C_51)
      | k4_xboole_0(k2_tarski(A_52,B_50),C_51) = k1_tarski(A_52)
      | r2_hidden(A_52,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_312,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_28])).

tff(c_320,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_312])).

tff(c_326,plain,(
    ! [A_53,B_54,C_55] :
      ( k4_xboole_0(k2_tarski(A_53,B_54),C_55) = k2_tarski(A_53,B_54)
      | r2_hidden(B_54,C_55)
      | r2_hidden(A_53,C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_369,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_24])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_320,c_369])).

tff(c_404,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_405,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_568,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r2_hidden(A_77,C_78)
      | k4_xboole_0(k2_tarski(A_77,B_79),C_78) = k1_tarski(B_79)
      | r2_hidden(B_79,C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_243])).

tff(c_26,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_620,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_26])).

tff(c_658,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_620])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_658])).

%------------------------------------------------------------------------------
