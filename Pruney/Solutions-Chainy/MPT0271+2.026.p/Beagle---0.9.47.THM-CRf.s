%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:04 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 10.56s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 126 expanded)
%              Number of leaves         :   39 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 136 expanded)
%              Number of equality atoms :   52 (  81 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_74,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_139,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_40,plain,(
    ! [C_28] : r2_hidden(C_28,k1_tarski(C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_140,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_284,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_301,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k5_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_284])).

tff(c_304,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_301])).

tff(c_399,plain,(
    ! [D_91,B_92,A_93] :
      ( ~ r2_hidden(D_91,B_92)
      | r2_hidden(D_91,k2_xboole_0(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_406,plain,(
    ! [D_94] :
      ( ~ r2_hidden(D_94,k1_tarski('#skF_7'))
      | r2_hidden(D_94,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_399])).

tff(c_410,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_406])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_410])).

tff(c_415,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_32,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_525,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_tarski(A_104),B_105)
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_532,plain,(
    ! [A_104,B_105] :
      ( k2_xboole_0(k1_tarski(A_104),B_105) = B_105
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_525,c_26])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_885,plain,(
    ! [A_133,B_134,C_135] : k5_xboole_0(k5_xboole_0(A_133,B_134),C_135) = k5_xboole_0(A_133,k5_xboole_0(B_134,C_135)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k2_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10784,plain,(
    ! [A_7063,B_7064] : k5_xboole_0(A_7063,k5_xboole_0(B_7064,k2_xboole_0(A_7063,B_7064))) = k3_xboole_0(A_7063,B_7064) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_34])).

tff(c_417,plain,(
    ! [B_95,A_96] : k5_xboole_0(B_95,A_96) = k5_xboole_0(A_96,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_433,plain,(
    ! [A_96] : k5_xboole_0(k1_xboole_0,A_96) = A_96 ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_28])).

tff(c_1006,plain,(
    ! [A_19,C_135] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_135)) = k5_xboole_0(k1_xboole_0,C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_885])).

tff(c_1019,plain,(
    ! [A_19,C_135] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_135)) = C_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_1006])).

tff(c_10834,plain,(
    ! [B_7064,A_7063] : k5_xboole_0(B_7064,k2_xboole_0(A_7063,B_7064)) = k5_xboole_0(A_7063,k3_xboole_0(A_7063,B_7064)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10784,c_1019])).

tff(c_10968,plain,(
    ! [B_7120,A_7121] : k5_xboole_0(B_7120,k2_xboole_0(A_7121,B_7120)) = k4_xboole_0(A_7121,B_7120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10834])).

tff(c_11103,plain,(
    ! [B_105,A_104] :
      ( k5_xboole_0(B_105,B_105) = k4_xboole_0(k1_tarski(A_104),B_105)
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_10968])).

tff(c_12337,plain,(
    ! [A_7462,B_7463] :
      ( k4_xboole_0(k1_tarski(A_7462),B_7463) = k1_xboole_0
      | ~ r2_hidden(A_7462,B_7463) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11103])).

tff(c_416,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_573,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_76])).

tff(c_12402,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12337,c_573])).

tff(c_12508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_12402])).

tff(c_12509,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_12611,plain,(
    ! [A_7526,B_7527] :
      ( r1_tarski(k1_tarski(A_7526),B_7527)
      | ~ r2_hidden(A_7526,B_7527) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12618,plain,(
    ! [A_7526,B_7527] :
      ( k2_xboole_0(k1_tarski(A_7526),B_7527) = B_7527
      | ~ r2_hidden(A_7526,B_7527) ) ),
    inference(resolution,[status(thm)],[c_12611,c_26])).

tff(c_13096,plain,(
    ! [A_7559,B_7560] : k5_xboole_0(k5_xboole_0(A_7559,B_7560),k2_xboole_0(A_7559,B_7560)) = k3_xboole_0(A_7559,B_7560) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21196,plain,(
    ! [A_13581,B_13582] : k5_xboole_0(A_13581,k5_xboole_0(B_13582,k2_xboole_0(A_13581,B_13582))) = k3_xboole_0(A_13581,B_13582) ),
    inference(superposition,[status(thm),theory(equality)],[c_13096,c_30])).

tff(c_12512,plain,(
    ! [B_7519,A_7520] : k5_xboole_0(B_7519,A_7520) = k5_xboole_0(A_7520,B_7519) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12528,plain,(
    ! [A_7520] : k5_xboole_0(k1_xboole_0,A_7520) = A_7520 ),
    inference(superposition,[status(thm),theory(equality)],[c_12512,c_28])).

tff(c_12839,plain,(
    ! [A_7552,B_7553,C_7554] : k5_xboole_0(k5_xboole_0(A_7552,B_7553),C_7554) = k5_xboole_0(A_7552,k5_xboole_0(B_7553,C_7554)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12925,plain,(
    ! [A_19,C_7554] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_7554)) = k5_xboole_0(k1_xboole_0,C_7554) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12839])).

tff(c_12938,plain,(
    ! [A_19,C_7554] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_7554)) = C_7554 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12528,c_12925])).

tff(c_21249,plain,(
    ! [B_13582,A_13581] : k5_xboole_0(B_13582,k2_xboole_0(A_13581,B_13582)) = k5_xboole_0(A_13581,k3_xboole_0(A_13581,B_13582)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21196,c_12938])).

tff(c_21371,plain,(
    ! [B_13638,A_13639] : k5_xboole_0(B_13638,k2_xboole_0(A_13639,B_13638)) = k4_xboole_0(A_13639,B_13638) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_21249])).

tff(c_21495,plain,(
    ! [B_7527,A_7526] :
      ( k5_xboole_0(B_7527,B_7527) = k4_xboole_0(k1_tarski(A_7526),B_7527)
      | ~ r2_hidden(A_7526,B_7527) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12618,c_21371])).

tff(c_22257,plain,(
    ! [A_13923,B_13924] :
      ( k4_xboole_0(k1_tarski(A_13923),B_13924) = k1_xboole_0
      | ~ r2_hidden(A_13923,B_13924) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_21495])).

tff(c_12510,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12634,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12510,c_72])).

tff(c_22321,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_22257,c_12634])).

tff(c_22421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12509,c_22321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.49/4.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.49/4.03  
% 10.49/4.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.49/4.03  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 10.49/4.03  
% 10.49/4.03  %Foreground sorts:
% 10.49/4.03  
% 10.49/4.03  
% 10.49/4.03  %Background operators:
% 10.49/4.03  
% 10.49/4.03  
% 10.49/4.03  %Foreground operators:
% 10.49/4.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.49/4.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.49/4.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.49/4.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.49/4.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.49/4.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.49/4.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.49/4.03  tff('#skF_7', type, '#skF_7': $i).
% 10.49/4.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.49/4.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.49/4.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.49/4.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.49/4.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.49/4.03  tff('#skF_5', type, '#skF_5': $i).
% 10.49/4.03  tff('#skF_6', type, '#skF_6': $i).
% 10.49/4.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.49/4.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.49/4.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.49/4.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.49/4.03  tff('#skF_8', type, '#skF_8': $i).
% 10.49/4.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.49/4.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.49/4.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.49/4.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.49/4.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.49/4.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.49/4.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.49/4.03  
% 10.56/4.05  tff(f_88, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 10.56/4.05  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.56/4.05  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.56/4.05  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.56/4.05  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 10.56/4.05  tff(f_50, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.56/4.05  tff(f_79, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.56/4.05  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.56/4.05  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.56/4.05  tff(f_48, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.56/4.05  tff(f_52, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.56/4.05  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.56/4.05  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.56/4.05  tff(c_139, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_74])).
% 10.56/4.05  tff(c_40, plain, (![C_28]: (r2_hidden(C_28, k1_tarski(C_28)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.56/4.05  tff(c_28, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.56/4.05  tff(c_78, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.56/4.05  tff(c_140, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78])).
% 10.56/4.05  tff(c_284, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.56/4.05  tff(c_301, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k5_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_284])).
% 10.56/4.05  tff(c_304, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_301])).
% 10.56/4.05  tff(c_399, plain, (![D_91, B_92, A_93]: (~r2_hidden(D_91, B_92) | r2_hidden(D_91, k2_xboole_0(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.56/4.05  tff(c_406, plain, (![D_94]: (~r2_hidden(D_94, k1_tarski('#skF_7')) | r2_hidden(D_94, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_304, c_399])).
% 10.56/4.05  tff(c_410, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_406])).
% 10.56/4.05  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_410])).
% 10.56/4.05  tff(c_415, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 10.56/4.05  tff(c_32, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.56/4.05  tff(c_525, plain, (![A_104, B_105]: (r1_tarski(k1_tarski(A_104), B_105) | ~r2_hidden(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.56/4.05  tff(c_26, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.56/4.05  tff(c_532, plain, (![A_104, B_105]: (k2_xboole_0(k1_tarski(A_104), B_105)=B_105 | ~r2_hidden(A_104, B_105))), inference(resolution, [status(thm)], [c_525, c_26])).
% 10.56/4.05  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.56/4.05  tff(c_885, plain, (![A_133, B_134, C_135]: (k5_xboole_0(k5_xboole_0(A_133, B_134), C_135)=k5_xboole_0(A_133, k5_xboole_0(B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.56/4.05  tff(c_34, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k2_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.56/4.05  tff(c_10784, plain, (![A_7063, B_7064]: (k5_xboole_0(A_7063, k5_xboole_0(B_7064, k2_xboole_0(A_7063, B_7064)))=k3_xboole_0(A_7063, B_7064))), inference(superposition, [status(thm), theory('equality')], [c_885, c_34])).
% 10.56/4.05  tff(c_417, plain, (![B_95, A_96]: (k5_xboole_0(B_95, A_96)=k5_xboole_0(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.56/4.05  tff(c_433, plain, (![A_96]: (k5_xboole_0(k1_xboole_0, A_96)=A_96)), inference(superposition, [status(thm), theory('equality')], [c_417, c_28])).
% 10.56/4.05  tff(c_1006, plain, (![A_19, C_135]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_135))=k5_xboole_0(k1_xboole_0, C_135))), inference(superposition, [status(thm), theory('equality')], [c_32, c_885])).
% 10.56/4.05  tff(c_1019, plain, (![A_19, C_135]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_135))=C_135)), inference(demodulation, [status(thm), theory('equality')], [c_433, c_1006])).
% 10.56/4.05  tff(c_10834, plain, (![B_7064, A_7063]: (k5_xboole_0(B_7064, k2_xboole_0(A_7063, B_7064))=k5_xboole_0(A_7063, k3_xboole_0(A_7063, B_7064)))), inference(superposition, [status(thm), theory('equality')], [c_10784, c_1019])).
% 10.56/4.05  tff(c_10968, plain, (![B_7120, A_7121]: (k5_xboole_0(B_7120, k2_xboole_0(A_7121, B_7120))=k4_xboole_0(A_7121, B_7120))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10834])).
% 10.56/4.05  tff(c_11103, plain, (![B_105, A_104]: (k5_xboole_0(B_105, B_105)=k4_xboole_0(k1_tarski(A_104), B_105) | ~r2_hidden(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_532, c_10968])).
% 10.56/4.05  tff(c_12337, plain, (![A_7462, B_7463]: (k4_xboole_0(k1_tarski(A_7462), B_7463)=k1_xboole_0 | ~r2_hidden(A_7462, B_7463))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11103])).
% 10.56/4.05  tff(c_416, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 10.56/4.05  tff(c_76, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.56/4.05  tff(c_573, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_416, c_76])).
% 10.56/4.05  tff(c_12402, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12337, c_573])).
% 10.56/4.05  tff(c_12508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_415, c_12402])).
% 10.56/4.05  tff(c_12509, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 10.56/4.05  tff(c_12611, plain, (![A_7526, B_7527]: (r1_tarski(k1_tarski(A_7526), B_7527) | ~r2_hidden(A_7526, B_7527))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.56/4.05  tff(c_12618, plain, (![A_7526, B_7527]: (k2_xboole_0(k1_tarski(A_7526), B_7527)=B_7527 | ~r2_hidden(A_7526, B_7527))), inference(resolution, [status(thm)], [c_12611, c_26])).
% 10.56/4.05  tff(c_13096, plain, (![A_7559, B_7560]: (k5_xboole_0(k5_xboole_0(A_7559, B_7560), k2_xboole_0(A_7559, B_7560))=k3_xboole_0(A_7559, B_7560))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.56/4.05  tff(c_30, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.56/4.05  tff(c_21196, plain, (![A_13581, B_13582]: (k5_xboole_0(A_13581, k5_xboole_0(B_13582, k2_xboole_0(A_13581, B_13582)))=k3_xboole_0(A_13581, B_13582))), inference(superposition, [status(thm), theory('equality')], [c_13096, c_30])).
% 10.56/4.05  tff(c_12512, plain, (![B_7519, A_7520]: (k5_xboole_0(B_7519, A_7520)=k5_xboole_0(A_7520, B_7519))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.56/4.05  tff(c_12528, plain, (![A_7520]: (k5_xboole_0(k1_xboole_0, A_7520)=A_7520)), inference(superposition, [status(thm), theory('equality')], [c_12512, c_28])).
% 10.56/4.05  tff(c_12839, plain, (![A_7552, B_7553, C_7554]: (k5_xboole_0(k5_xboole_0(A_7552, B_7553), C_7554)=k5_xboole_0(A_7552, k5_xboole_0(B_7553, C_7554)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.56/4.05  tff(c_12925, plain, (![A_19, C_7554]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_7554))=k5_xboole_0(k1_xboole_0, C_7554))), inference(superposition, [status(thm), theory('equality')], [c_32, c_12839])).
% 10.56/4.05  tff(c_12938, plain, (![A_19, C_7554]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_7554))=C_7554)), inference(demodulation, [status(thm), theory('equality')], [c_12528, c_12925])).
% 10.56/4.05  tff(c_21249, plain, (![B_13582, A_13581]: (k5_xboole_0(B_13582, k2_xboole_0(A_13581, B_13582))=k5_xboole_0(A_13581, k3_xboole_0(A_13581, B_13582)))), inference(superposition, [status(thm), theory('equality')], [c_21196, c_12938])).
% 10.56/4.05  tff(c_21371, plain, (![B_13638, A_13639]: (k5_xboole_0(B_13638, k2_xboole_0(A_13639, B_13638))=k4_xboole_0(A_13639, B_13638))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_21249])).
% 10.56/4.05  tff(c_21495, plain, (![B_7527, A_7526]: (k5_xboole_0(B_7527, B_7527)=k4_xboole_0(k1_tarski(A_7526), B_7527) | ~r2_hidden(A_7526, B_7527))), inference(superposition, [status(thm), theory('equality')], [c_12618, c_21371])).
% 10.56/4.05  tff(c_22257, plain, (![A_13923, B_13924]: (k4_xboole_0(k1_tarski(A_13923), B_13924)=k1_xboole_0 | ~r2_hidden(A_13923, B_13924))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_21495])).
% 10.56/4.05  tff(c_12510, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_74])).
% 10.56/4.05  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.56/4.05  tff(c_12634, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12510, c_72])).
% 10.56/4.05  tff(c_22321, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_22257, c_12634])).
% 10.56/4.05  tff(c_22421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12509, c_22321])).
% 10.56/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.56/4.05  
% 10.56/4.05  Inference rules
% 10.56/4.05  ----------------------
% 10.56/4.05  #Ref     : 0
% 10.56/4.05  #Sup     : 5172
% 10.56/4.05  #Fact    : 12
% 10.56/4.05  #Define  : 0
% 10.56/4.05  #Split   : 8
% 10.56/4.05  #Chain   : 0
% 10.56/4.05  #Close   : 0
% 10.56/4.05  
% 10.56/4.05  Ordering : KBO
% 10.56/4.05  
% 10.56/4.05  Simplification rules
% 10.56/4.05  ----------------------
% 10.56/4.05  #Subsume      : 274
% 10.56/4.05  #Demod        : 4744
% 10.56/4.05  #Tautology    : 2919
% 10.56/4.05  #SimpNegUnit  : 2
% 10.56/4.05  #BackRed      : 3
% 10.56/4.05  
% 10.56/4.05  #Partial instantiations: 5368
% 10.56/4.05  #Strategies tried      : 1
% 10.56/4.05  
% 10.56/4.05  Timing (in seconds)
% 10.56/4.05  ----------------------
% 10.56/4.05  Preprocessing        : 0.36
% 10.56/4.05  Parsing              : 0.19
% 10.56/4.05  CNF conversion       : 0.03
% 10.56/4.05  Main loop            : 2.87
% 10.56/4.05  Inferencing          : 0.84
% 10.56/4.05  Reduction            : 1.40
% 10.56/4.05  Demodulation         : 1.23
% 10.56/4.05  BG Simplification    : 0.09
% 10.56/4.05  Subsumption          : 0.39
% 10.56/4.06  Abstraction          : 0.12
% 10.56/4.06  MUC search           : 0.00
% 10.56/4.06  Cooper               : 0.00
% 10.56/4.06  Total                : 3.27
% 10.56/4.06  Index Insertion      : 0.00
% 10.56/4.06  Index Deletion       : 0.00
% 10.56/4.06  Index Matching       : 0.00
% 10.56/4.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
