%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 15.27s
% Output     : CNFRefutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 197 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 413 expanded)
%              Number of equality atoms :   11 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(B_33,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_33,A_32] : k3_xboole_0(B_33,A_32) = k3_xboole_0(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_8])).

tff(c_169,plain,(
    ! [C_45,A_46,B_47] :
      ( k7_relat_1(k7_relat_1(C_45,A_46),B_47) = k7_relat_1(C_45,k3_xboole_0(A_46,B_47))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k7_relat_1(B_21,A_20),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    ! [C_48,A_49,B_50] :
      ( r1_tarski(k7_relat_1(C_48,k3_xboole_0(A_49,B_50)),k7_relat_1(C_48,A_49))
      | ~ v1_relat_1(k7_relat_1(C_48,A_49))
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_20])).

tff(c_203,plain,(
    ! [C_48,B_33,A_32] :
      ( r1_tarski(k7_relat_1(C_48,k3_xboole_0(B_33,A_32)),k7_relat_1(C_48,A_32))
      | ~ v1_relat_1(k7_relat_1(C_48,A_32))
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_193])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k2_relat_1(A_43),k2_relat_1(B_44))
      | ~ r1_tarski(A_43,B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6120,plain,(
    ! [A_230,B_231,A_232] :
      ( r1_tarski(k2_relat_1(A_230),k9_relat_1(B_231,A_232))
      | ~ r1_tarski(A_230,k7_relat_1(B_231,A_232))
      | ~ v1_relat_1(k7_relat_1(B_231,A_232))
      | ~ v1_relat_1(A_230)
      | ~ v1_relat_1(B_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_162])).

tff(c_10577,plain,(
    ! [B_342,A_343,B_344,A_345] :
      ( r1_tarski(k9_relat_1(B_342,A_343),k9_relat_1(B_344,A_345))
      | ~ r1_tarski(k7_relat_1(B_342,A_343),k7_relat_1(B_344,A_345))
      | ~ v1_relat_1(k7_relat_1(B_344,A_345))
      | ~ v1_relat_1(k7_relat_1(B_342,A_343))
      | ~ v1_relat_1(B_344)
      | ~ v1_relat_1(B_342) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6120])).

tff(c_181,plain,(
    ! [C_45,A_46,B_47] :
      ( r1_tarski(k7_relat_1(C_45,k3_xboole_0(A_46,B_47)),k7_relat_1(C_45,A_46))
      | ~ v1_relat_1(k7_relat_1(C_45,A_46))
      | ~ v1_relat_1(C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_20])).

tff(c_298,plain,(
    ! [B_63,A_64,B_65] :
      ( r1_tarski(k9_relat_1(B_63,A_64),k2_relat_1(B_65))
      | ~ r1_tarski(k7_relat_1(B_63,A_64),B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(k7_relat_1(B_63,A_64))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_162])).

tff(c_5683,plain,(
    ! [B_202,A_203,B_204,A_205] :
      ( r1_tarski(k9_relat_1(B_202,A_203),k9_relat_1(B_204,A_205))
      | ~ r1_tarski(k7_relat_1(B_202,A_203),k7_relat_1(B_204,A_205))
      | ~ v1_relat_1(k7_relat_1(B_204,A_205))
      | ~ v1_relat_1(k7_relat_1(B_202,A_203))
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(B_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_298])).

tff(c_150,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,k3_xboole_0(B_39,C_40))
      | ~ r1_tarski(A_38,C_40)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_160,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_150,c_22])).

tff(c_221,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_5686,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5683,c_221])).

tff(c_5869,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5686])).

tff(c_5870,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5869])).

tff(c_5873,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5870])).

tff(c_5877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5873])).

tff(c_5878,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5869])).

tff(c_5880,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5878])).

tff(c_5883,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_181,c_5880])).

tff(c_5886,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5883])).

tff(c_5889,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5886])).

tff(c_5893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5889])).

tff(c_5894,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5878])).

tff(c_5898,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5894])).

tff(c_5902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5898])).

tff(c_5903,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_10580,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10577,c_5903])).

tff(c_10745,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10580])).

tff(c_10746,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_10745])).

tff(c_10749,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_10746])).

tff(c_10753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10749])).

tff(c_10754,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_10745])).

tff(c_10756,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10754])).

tff(c_10759,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_203,c_10756])).

tff(c_10762,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10759])).

tff(c_10765,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_10762])).

tff(c_10769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10765])).

tff(c_10770,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_10754])).

tff(c_10774,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_10770])).

tff(c_10778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.27/5.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.27/5.38  
% 15.27/5.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.27/5.39  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 15.27/5.39  
% 15.27/5.39  %Foreground sorts:
% 15.27/5.39  
% 15.27/5.39  
% 15.27/5.39  %Background operators:
% 15.27/5.39  
% 15.27/5.39  
% 15.27/5.39  %Foreground operators:
% 15.27/5.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.27/5.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.27/5.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.27/5.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.27/5.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.27/5.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.27/5.39  tff('#skF_2', type, '#skF_2': $i).
% 15.27/5.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.27/5.39  tff('#skF_3', type, '#skF_3': $i).
% 15.27/5.39  tff('#skF_1', type, '#skF_1': $i).
% 15.27/5.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.27/5.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.27/5.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.27/5.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.27/5.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.27/5.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.27/5.39  
% 15.46/5.41  tff(f_69, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 15.46/5.41  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 15.46/5.41  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.46/5.41  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.46/5.41  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 15.46/5.41  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 15.46/5.41  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 15.46/5.41  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 15.46/5.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 15.46/5.41  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.46/5.41  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.46/5.41  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.46/5.41  tff(c_59, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.46/5.41  tff(c_84, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(B_33, A_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 15.46/5.41  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.46/5.41  tff(c_90, plain, (![B_33, A_32]: (k3_xboole_0(B_33, A_32)=k3_xboole_0(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_84, c_8])).
% 15.46/5.41  tff(c_169, plain, (![C_45, A_46, B_47]: (k7_relat_1(k7_relat_1(C_45, A_46), B_47)=k7_relat_1(C_45, k3_xboole_0(A_46, B_47)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.46/5.41  tff(c_20, plain, (![B_21, A_20]: (r1_tarski(k7_relat_1(B_21, A_20), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.46/5.41  tff(c_193, plain, (![C_48, A_49, B_50]: (r1_tarski(k7_relat_1(C_48, k3_xboole_0(A_49, B_50)), k7_relat_1(C_48, A_49)) | ~v1_relat_1(k7_relat_1(C_48, A_49)) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_169, c_20])).
% 15.46/5.41  tff(c_203, plain, (![C_48, B_33, A_32]: (r1_tarski(k7_relat_1(C_48, k3_xboole_0(B_33, A_32)), k7_relat_1(C_48, A_32)) | ~v1_relat_1(k7_relat_1(C_48, A_32)) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_90, c_193])).
% 15.46/5.41  tff(c_14, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.46/5.41  tff(c_162, plain, (![A_43, B_44]: (r1_tarski(k2_relat_1(A_43), k2_relat_1(B_44)) | ~r1_tarski(A_43, B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.46/5.41  tff(c_6120, plain, (![A_230, B_231, A_232]: (r1_tarski(k2_relat_1(A_230), k9_relat_1(B_231, A_232)) | ~r1_tarski(A_230, k7_relat_1(B_231, A_232)) | ~v1_relat_1(k7_relat_1(B_231, A_232)) | ~v1_relat_1(A_230) | ~v1_relat_1(B_231))), inference(superposition, [status(thm), theory('equality')], [c_14, c_162])).
% 15.46/5.41  tff(c_10577, plain, (![B_342, A_343, B_344, A_345]: (r1_tarski(k9_relat_1(B_342, A_343), k9_relat_1(B_344, A_345)) | ~r1_tarski(k7_relat_1(B_342, A_343), k7_relat_1(B_344, A_345)) | ~v1_relat_1(k7_relat_1(B_344, A_345)) | ~v1_relat_1(k7_relat_1(B_342, A_343)) | ~v1_relat_1(B_344) | ~v1_relat_1(B_342))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6120])).
% 15.46/5.41  tff(c_181, plain, (![C_45, A_46, B_47]: (r1_tarski(k7_relat_1(C_45, k3_xboole_0(A_46, B_47)), k7_relat_1(C_45, A_46)) | ~v1_relat_1(k7_relat_1(C_45, A_46)) | ~v1_relat_1(C_45))), inference(superposition, [status(thm), theory('equality')], [c_169, c_20])).
% 15.46/5.41  tff(c_298, plain, (![B_63, A_64, B_65]: (r1_tarski(k9_relat_1(B_63, A_64), k2_relat_1(B_65)) | ~r1_tarski(k7_relat_1(B_63, A_64), B_65) | ~v1_relat_1(B_65) | ~v1_relat_1(k7_relat_1(B_63, A_64)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_162])).
% 15.46/5.41  tff(c_5683, plain, (![B_202, A_203, B_204, A_205]: (r1_tarski(k9_relat_1(B_202, A_203), k9_relat_1(B_204, A_205)) | ~r1_tarski(k7_relat_1(B_202, A_203), k7_relat_1(B_204, A_205)) | ~v1_relat_1(k7_relat_1(B_204, A_205)) | ~v1_relat_1(k7_relat_1(B_202, A_203)) | ~v1_relat_1(B_202) | ~v1_relat_1(B_204))), inference(superposition, [status(thm), theory('equality')], [c_14, c_298])).
% 15.46/5.41  tff(c_150, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, k3_xboole_0(B_39, C_40)) | ~r1_tarski(A_38, C_40) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.46/5.41  tff(c_22, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.46/5.41  tff(c_160, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_150, c_22])).
% 15.46/5.41  tff(c_221, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_160])).
% 15.46/5.41  tff(c_5686, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5683, c_221])).
% 15.46/5.41  tff(c_5869, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5686])).
% 15.46/5.41  tff(c_5870, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5869])).
% 15.46/5.41  tff(c_5873, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5870])).
% 15.46/5.41  tff(c_5877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_5873])).
% 15.46/5.41  tff(c_5878, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_5869])).
% 15.46/5.41  tff(c_5880, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5878])).
% 15.46/5.41  tff(c_5883, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_181, c_5880])).
% 15.46/5.41  tff(c_5886, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5883])).
% 15.46/5.41  tff(c_5889, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5886])).
% 15.46/5.41  tff(c_5893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_5889])).
% 15.46/5.41  tff(c_5894, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_5878])).
% 15.46/5.41  tff(c_5898, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5894])).
% 15.46/5.41  tff(c_5902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_5898])).
% 15.46/5.41  tff(c_5903, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_160])).
% 15.46/5.41  tff(c_10580, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10577, c_5903])).
% 15.46/5.41  tff(c_10745, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10580])).
% 15.46/5.41  tff(c_10746, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_10745])).
% 15.46/5.41  tff(c_10749, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_10746])).
% 15.46/5.41  tff(c_10753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_10749])).
% 15.46/5.41  tff(c_10754, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_10745])).
% 15.46/5.41  tff(c_10756, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_10754])).
% 15.46/5.41  tff(c_10759, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_203, c_10756])).
% 15.46/5.41  tff(c_10762, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10759])).
% 15.46/5.41  tff(c_10765, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_10762])).
% 15.46/5.41  tff(c_10769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_10765])).
% 15.46/5.41  tff(c_10770, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_10754])).
% 15.46/5.41  tff(c_10774, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_10770])).
% 15.46/5.41  tff(c_10778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_10774])).
% 15.46/5.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/5.41  
% 15.46/5.41  Inference rules
% 15.46/5.41  ----------------------
% 15.46/5.41  #Ref     : 0
% 15.46/5.41  #Sup     : 3095
% 15.46/5.41  #Fact    : 0
% 15.46/5.41  #Define  : 0
% 15.46/5.41  #Split   : 5
% 15.46/5.41  #Chain   : 0
% 15.46/5.41  #Close   : 0
% 15.46/5.41  
% 15.46/5.41  Ordering : KBO
% 15.46/5.41  
% 15.46/5.41  Simplification rules
% 15.46/5.41  ----------------------
% 15.46/5.41  #Subsume      : 348
% 15.46/5.41  #Demod        : 13
% 15.46/5.41  #Tautology    : 211
% 15.46/5.41  #SimpNegUnit  : 0
% 15.46/5.41  #BackRed      : 0
% 15.46/5.41  
% 15.46/5.41  #Partial instantiations: 0
% 15.46/5.41  #Strategies tried      : 1
% 15.46/5.41  
% 15.46/5.41  Timing (in seconds)
% 15.46/5.41  ----------------------
% 15.46/5.42  Preprocessing        : 0.45
% 15.46/5.42  Parsing              : 0.24
% 15.46/5.42  CNF conversion       : 0.03
% 15.46/5.42  Main loop            : 4.06
% 15.46/5.42  Inferencing          : 1.56
% 15.46/5.42  Reduction            : 1.07
% 15.46/5.42  Demodulation         : 0.87
% 15.46/5.42  BG Simplification    : 0.30
% 15.46/5.42  Subsumption          : 0.95
% 15.46/5.42  Abstraction          : 0.29
% 15.46/5.42  MUC search           : 0.00
% 15.46/5.42  Cooper               : 0.00
% 15.46/5.42  Total                : 4.57
% 15.46/5.42  Index Insertion      : 0.00
% 15.46/5.42  Index Deletion       : 0.00
% 15.46/5.42  Index Matching       : 0.00
% 15.46/5.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
