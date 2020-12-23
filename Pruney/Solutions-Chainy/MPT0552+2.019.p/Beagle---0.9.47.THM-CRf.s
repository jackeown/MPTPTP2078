%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:59 EST 2020

% Result     : Theorem 9.87s
% Output     : CNFRefutation 9.87s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 186 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 386 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_18,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_18])).

tff(c_8001,plain,(
    ! [C_261,A_262,B_263] :
      ( k3_xboole_0(k7_relat_1(C_261,A_262),k7_relat_1(C_261,B_263)) = k7_relat_1(C_261,k3_xboole_0(A_262,B_263))
      | ~ v1_relat_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8477,plain,(
    ! [C_268,A_269,B_270] :
      ( r1_tarski(k7_relat_1(C_268,k3_xboole_0(A_269,B_270)),k7_relat_1(C_268,A_269))
      | ~ v1_relat_1(C_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_8])).

tff(c_8521,plain,(
    ! [C_268,A_43,B_42] :
      ( r1_tarski(k7_relat_1(C_268,k3_xboole_0(A_43,B_42)),k7_relat_1(C_268,B_42))
      | ~ v1_relat_1(C_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8477])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7759,plain,(
    ! [A_253,B_254] :
      ( r1_tarski(k2_relat_1(A_253),k2_relat_1(B_254))
      | ~ r1_tarski(A_253,B_254)
      | ~ v1_relat_1(B_254)
      | ~ v1_relat_1(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9797,plain,(
    ! [A_290,B_291,A_292] :
      ( r1_tarski(k2_relat_1(A_290),k9_relat_1(B_291,A_292))
      | ~ r1_tarski(A_290,k7_relat_1(B_291,A_292))
      | ~ v1_relat_1(k7_relat_1(B_291,A_292))
      | ~ v1_relat_1(A_290)
      | ~ v1_relat_1(B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7759])).

tff(c_14241,plain,(
    ! [B_400,A_401,B_402,A_403] :
      ( r1_tarski(k9_relat_1(B_400,A_401),k9_relat_1(B_402,A_403))
      | ~ r1_tarski(k7_relat_1(B_400,A_401),k7_relat_1(B_402,A_403))
      | ~ v1_relat_1(k7_relat_1(B_402,A_403))
      | ~ v1_relat_1(k7_relat_1(B_400,A_401))
      | ~ v1_relat_1(B_402)
      | ~ v1_relat_1(B_400) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9797])).

tff(c_942,plain,(
    ! [C_89,A_90,B_91] :
      ( k3_xboole_0(k7_relat_1(C_89,A_90),k7_relat_1(C_89,B_91)) = k7_relat_1(C_89,k3_xboole_0(A_90,B_91))
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1003,plain,(
    ! [C_89,A_90,B_91] :
      ( r1_tarski(k7_relat_1(C_89,k3_xboole_0(A_90,B_91)),k7_relat_1(C_89,A_90))
      | ~ v1_relat_1(C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_8])).

tff(c_612,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k2_relat_1(A_79),k2_relat_1(B_80))
      | ~ r1_tarski(A_79,B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3262,plain,(
    ! [A_132,B_133,A_134] :
      ( r1_tarski(k2_relat_1(A_132),k9_relat_1(B_133,A_134))
      | ~ r1_tarski(A_132,k7_relat_1(B_133,A_134))
      | ~ v1_relat_1(k7_relat_1(B_133,A_134))
      | ~ v1_relat_1(A_132)
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_612])).

tff(c_7311,plain,(
    ! [B_237,A_238,B_239,A_240] :
      ( r1_tarski(k9_relat_1(B_237,A_238),k9_relat_1(B_239,A_240))
      | ~ r1_tarski(k7_relat_1(B_237,A_238),k7_relat_1(B_239,A_240))
      | ~ v1_relat_1(k7_relat_1(B_239,A_240))
      | ~ v1_relat_1(k7_relat_1(B_237,A_238))
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(B_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3262])).

tff(c_242,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k3_xboole_0(B_66,C_67))
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_283,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_242,c_32])).

tff(c_347,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_7321,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7311,c_347])).

tff(c_7335,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7321])).

tff(c_7339,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7335])).

tff(c_7342,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_7339])).

tff(c_7346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7342])).

tff(c_7347,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7335])).

tff(c_7349,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_7347])).

tff(c_7352,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1003,c_7349])).

tff(c_7356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7352])).

tff(c_7357,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7347])).

tff(c_7361,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_7357])).

tff(c_7365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7361])).

tff(c_7366,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_14254,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14241,c_7366])).

tff(c_14271,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14254])).

tff(c_14275,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_14271])).

tff(c_14278,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_14275])).

tff(c_14282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14278])).

tff(c_14283,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14271])).

tff(c_14285,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14283])).

tff(c_14288,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8521,c_14285])).

tff(c_14292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14288])).

tff(c_14293,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14283])).

tff(c_14297,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_14293])).

tff(c_14301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.87/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.27  
% 9.87/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.28  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 9.87/3.28  
% 9.87/3.28  %Foreground sorts:
% 9.87/3.28  
% 9.87/3.28  
% 9.87/3.28  %Background operators:
% 9.87/3.28  
% 9.87/3.28  
% 9.87/3.28  %Foreground operators:
% 9.87/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.87/3.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.87/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.87/3.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.87/3.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.87/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.87/3.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.87/3.28  tff('#skF_2', type, '#skF_2': $i).
% 9.87/3.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.87/3.28  tff('#skF_3', type, '#skF_3': $i).
% 9.87/3.28  tff('#skF_1', type, '#skF_1': $i).
% 9.87/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.87/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.87/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.87/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.87/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.87/3.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.87/3.28  
% 9.87/3.29  tff(f_79, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 9.87/3.29  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.87/3.29  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.87/3.29  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.87/3.29  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 9.87/3.29  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.87/3.29  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.87/3.29  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 9.87/3.29  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 9.87/3.29  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.87/3.29  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.87/3.29  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.87/3.29  tff(c_82, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.87/3.29  tff(c_97, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_12, c_82])).
% 9.87/3.29  tff(c_18, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.87/3.29  tff(c_103, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_97, c_18])).
% 9.87/3.29  tff(c_8001, plain, (![C_261, A_262, B_263]: (k3_xboole_0(k7_relat_1(C_261, A_262), k7_relat_1(C_261, B_263))=k7_relat_1(C_261, k3_xboole_0(A_262, B_263)) | ~v1_relat_1(C_261))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.87/3.29  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.87/3.29  tff(c_8477, plain, (![C_268, A_269, B_270]: (r1_tarski(k7_relat_1(C_268, k3_xboole_0(A_269, B_270)), k7_relat_1(C_268, A_269)) | ~v1_relat_1(C_268))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_8])).
% 9.87/3.29  tff(c_8521, plain, (![C_268, A_43, B_42]: (r1_tarski(k7_relat_1(C_268, k3_xboole_0(A_43, B_42)), k7_relat_1(C_268, B_42)) | ~v1_relat_1(C_268))), inference(superposition, [status(thm), theory('equality')], [c_103, c_8477])).
% 9.87/3.29  tff(c_26, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.87/3.29  tff(c_7759, plain, (![A_253, B_254]: (r1_tarski(k2_relat_1(A_253), k2_relat_1(B_254)) | ~r1_tarski(A_253, B_254) | ~v1_relat_1(B_254) | ~v1_relat_1(A_253))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.87/3.29  tff(c_9797, plain, (![A_290, B_291, A_292]: (r1_tarski(k2_relat_1(A_290), k9_relat_1(B_291, A_292)) | ~r1_tarski(A_290, k7_relat_1(B_291, A_292)) | ~v1_relat_1(k7_relat_1(B_291, A_292)) | ~v1_relat_1(A_290) | ~v1_relat_1(B_291))), inference(superposition, [status(thm), theory('equality')], [c_26, c_7759])).
% 9.87/3.29  tff(c_14241, plain, (![B_400, A_401, B_402, A_403]: (r1_tarski(k9_relat_1(B_400, A_401), k9_relat_1(B_402, A_403)) | ~r1_tarski(k7_relat_1(B_400, A_401), k7_relat_1(B_402, A_403)) | ~v1_relat_1(k7_relat_1(B_402, A_403)) | ~v1_relat_1(k7_relat_1(B_400, A_401)) | ~v1_relat_1(B_402) | ~v1_relat_1(B_400))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9797])).
% 9.87/3.29  tff(c_942, plain, (![C_89, A_90, B_91]: (k3_xboole_0(k7_relat_1(C_89, A_90), k7_relat_1(C_89, B_91))=k7_relat_1(C_89, k3_xboole_0(A_90, B_91)) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.87/3.29  tff(c_1003, plain, (![C_89, A_90, B_91]: (r1_tarski(k7_relat_1(C_89, k3_xboole_0(A_90, B_91)), k7_relat_1(C_89, A_90)) | ~v1_relat_1(C_89))), inference(superposition, [status(thm), theory('equality')], [c_942, c_8])).
% 9.87/3.29  tff(c_612, plain, (![A_79, B_80]: (r1_tarski(k2_relat_1(A_79), k2_relat_1(B_80)) | ~r1_tarski(A_79, B_80) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.87/3.29  tff(c_3262, plain, (![A_132, B_133, A_134]: (r1_tarski(k2_relat_1(A_132), k9_relat_1(B_133, A_134)) | ~r1_tarski(A_132, k7_relat_1(B_133, A_134)) | ~v1_relat_1(k7_relat_1(B_133, A_134)) | ~v1_relat_1(A_132) | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_26, c_612])).
% 9.87/3.29  tff(c_7311, plain, (![B_237, A_238, B_239, A_240]: (r1_tarski(k9_relat_1(B_237, A_238), k9_relat_1(B_239, A_240)) | ~r1_tarski(k7_relat_1(B_237, A_238), k7_relat_1(B_239, A_240)) | ~v1_relat_1(k7_relat_1(B_239, A_240)) | ~v1_relat_1(k7_relat_1(B_237, A_238)) | ~v1_relat_1(B_239) | ~v1_relat_1(B_237))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3262])).
% 9.87/3.29  tff(c_242, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k3_xboole_0(B_66, C_67)) | ~r1_tarski(A_65, C_67) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.87/3.29  tff(c_32, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.87/3.29  tff(c_283, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_242, c_32])).
% 9.87/3.29  tff(c_347, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_283])).
% 9.87/3.29  tff(c_7321, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7311, c_347])).
% 9.87/3.29  tff(c_7335, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7321])).
% 9.87/3.29  tff(c_7339, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7335])).
% 9.87/3.29  tff(c_7342, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_7339])).
% 9.87/3.29  tff(c_7346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_7342])).
% 9.87/3.29  tff(c_7347, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_7335])).
% 9.87/3.29  tff(c_7349, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_7347])).
% 9.87/3.29  tff(c_7352, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1003, c_7349])).
% 9.87/3.29  tff(c_7356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_7352])).
% 9.87/3.29  tff(c_7357, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_7347])).
% 9.87/3.29  tff(c_7361, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_7357])).
% 9.87/3.29  tff(c_7365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_7361])).
% 9.87/3.29  tff(c_7366, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_283])).
% 9.87/3.29  tff(c_14254, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14241, c_7366])).
% 9.87/3.29  tff(c_14271, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14254])).
% 9.87/3.29  tff(c_14275, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_14271])).
% 9.87/3.29  tff(c_14278, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_14275])).
% 9.87/3.29  tff(c_14282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_14278])).
% 9.87/3.29  tff(c_14283, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_14271])).
% 9.87/3.29  tff(c_14285, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_14283])).
% 9.87/3.29  tff(c_14288, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8521, c_14285])).
% 9.87/3.29  tff(c_14292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_14288])).
% 9.87/3.29  tff(c_14293, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_14283])).
% 9.87/3.29  tff(c_14297, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_14293])).
% 9.87/3.29  tff(c_14301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_14297])).
% 9.87/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.29  
% 9.87/3.29  Inference rules
% 9.87/3.29  ----------------------
% 9.87/3.29  #Ref     : 0
% 9.87/3.29  #Sup     : 3701
% 9.87/3.29  #Fact    : 0
% 9.87/3.29  #Define  : 0
% 9.87/3.29  #Split   : 7
% 9.87/3.29  #Chain   : 0
% 9.87/3.29  #Close   : 0
% 9.87/3.29  
% 9.87/3.29  Ordering : KBO
% 9.87/3.29  
% 9.87/3.29  Simplification rules
% 9.87/3.29  ----------------------
% 9.87/3.29  #Subsume      : 1305
% 9.87/3.29  #Demod        : 3145
% 9.87/3.29  #Tautology    : 1430
% 9.87/3.29  #SimpNegUnit  : 8
% 9.87/3.29  #BackRed      : 0
% 9.87/3.29  
% 9.87/3.29  #Partial instantiations: 0
% 9.87/3.29  #Strategies tried      : 1
% 9.87/3.29  
% 9.87/3.29  Timing (in seconds)
% 9.87/3.29  ----------------------
% 9.87/3.29  Preprocessing        : 0.32
% 9.87/3.29  Parsing              : 0.17
% 9.87/3.29  CNF conversion       : 0.02
% 9.87/3.29  Main loop            : 2.20
% 9.87/3.29  Inferencing          : 0.58
% 9.87/3.29  Reduction            : 0.98
% 9.87/3.29  Demodulation         : 0.83
% 9.87/3.30  BG Simplification    : 0.07
% 9.87/3.30  Subsumption          : 0.47
% 9.87/3.30  Abstraction          : 0.12
% 9.87/3.30  MUC search           : 0.00
% 9.87/3.30  Cooper               : 0.00
% 9.87/3.30  Total                : 2.55
% 9.87/3.30  Index Insertion      : 0.00
% 9.87/3.30  Index Deletion       : 0.00
% 9.87/3.30  Index Matching       : 0.00
% 9.87/3.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
