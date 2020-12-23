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
% DateTime   : Thu Dec  3 10:00:57 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 185 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 387 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_20,plain,(
    ! [C_21,A_19,B_20] :
      ( r1_tarski(k7_relat_1(C_21,A_19),k7_relat_1(C_21,B_20))
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_231,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k2_relat_1(A_65),k2_relat_1(B_66))
      | ~ r1_tarski(A_65,B_66)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_352,plain,(
    ! [A_93,B_94,A_95] :
      ( r1_tarski(k2_relat_1(A_93),k9_relat_1(B_94,A_95))
      | ~ r1_tarski(A_93,k7_relat_1(B_94,A_95))
      | ~ v1_relat_1(k7_relat_1(B_94,A_95))
      | ~ v1_relat_1(A_93)
      | ~ v1_relat_1(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_231])).

tff(c_402,plain,(
    ! [B_114,A_115,B_116,A_117] :
      ( r1_tarski(k9_relat_1(B_114,A_115),k9_relat_1(B_116,A_117))
      | ~ r1_tarski(k7_relat_1(B_114,A_115),k7_relat_1(B_116,A_117))
      | ~ v1_relat_1(k7_relat_1(B_116,A_117))
      | ~ v1_relat_1(k7_relat_1(B_114,A_115))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_352])).

tff(c_266,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_tarski(k2_relat_1(A_77),k9_relat_1(B_78,A_79))
      | ~ r1_tarski(A_77,k7_relat_1(B_78,A_79))
      | ~ v1_relat_1(k7_relat_1(B_78,A_79))
      | ~ v1_relat_1(A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_231])).

tff(c_299,plain,(
    ! [B_86,A_87,B_88,A_89] :
      ( r1_tarski(k9_relat_1(B_86,A_87),k9_relat_1(B_88,A_89))
      | ~ r1_tarski(k7_relat_1(B_86,A_87),k7_relat_1(B_88,A_89))
      | ~ v1_relat_1(k7_relat_1(B_88,A_89))
      | ~ v1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_266])).

tff(c_206,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_220,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_206,c_28])).

tff(c_257,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_302,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_257])).

tff(c_308,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_302])).

tff(c_310,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_313,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_310])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_313])).

tff(c_318,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_320,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_323,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_320])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_323])).

tff(c_328,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_332,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_328])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_332])).

tff(c_337,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_405,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_337])).

tff(c_411,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_405])).

tff(c_413,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_416,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_413])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_416])).

tff(c_421,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_423,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_426,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_423])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_134,c_426])).

tff(c_431,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_435,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_431])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.81/1.38  
% 2.81/1.38  %Foreground sorts:
% 2.81/1.38  
% 2.81/1.38  
% 2.81/1.38  %Background operators:
% 2.81/1.38  
% 2.81/1.38  
% 2.81/1.38  %Foreground operators:
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.81/1.38  
% 2.81/1.39  tff(f_80, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 2.81/1.39  tff(f_54, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.81/1.39  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.81/1.39  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.81/1.39  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.81/1.39  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 2.81/1.39  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.81/1.39  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.81/1.39  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.81/1.39  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.39  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.39  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.39  tff(c_81, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.39  tff(c_96, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_81])).
% 2.81/1.39  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.39  tff(c_119, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_96, c_10])).
% 2.81/1.39  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.39  tff(c_134, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_119, c_2])).
% 2.81/1.39  tff(c_20, plain, (![C_21, A_19, B_20]: (r1_tarski(k7_relat_1(C_21, A_19), k7_relat_1(C_21, B_20)) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.81/1.39  tff(c_22, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.39  tff(c_231, plain, (![A_65, B_66]: (r1_tarski(k2_relat_1(A_65), k2_relat_1(B_66)) | ~r1_tarski(A_65, B_66) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.39  tff(c_352, plain, (![A_93, B_94, A_95]: (r1_tarski(k2_relat_1(A_93), k9_relat_1(B_94, A_95)) | ~r1_tarski(A_93, k7_relat_1(B_94, A_95)) | ~v1_relat_1(k7_relat_1(B_94, A_95)) | ~v1_relat_1(A_93) | ~v1_relat_1(B_94))), inference(superposition, [status(thm), theory('equality')], [c_22, c_231])).
% 2.81/1.39  tff(c_402, plain, (![B_114, A_115, B_116, A_117]: (r1_tarski(k9_relat_1(B_114, A_115), k9_relat_1(B_116, A_117)) | ~r1_tarski(k7_relat_1(B_114, A_115), k7_relat_1(B_116, A_117)) | ~v1_relat_1(k7_relat_1(B_116, A_117)) | ~v1_relat_1(k7_relat_1(B_114, A_115)) | ~v1_relat_1(B_116) | ~v1_relat_1(B_114))), inference(superposition, [status(thm), theory('equality')], [c_22, c_352])).
% 2.81/1.39  tff(c_266, plain, (![A_77, B_78, A_79]: (r1_tarski(k2_relat_1(A_77), k9_relat_1(B_78, A_79)) | ~r1_tarski(A_77, k7_relat_1(B_78, A_79)) | ~v1_relat_1(k7_relat_1(B_78, A_79)) | ~v1_relat_1(A_77) | ~v1_relat_1(B_78))), inference(superposition, [status(thm), theory('equality')], [c_22, c_231])).
% 2.81/1.39  tff(c_299, plain, (![B_86, A_87, B_88, A_89]: (r1_tarski(k9_relat_1(B_86, A_87), k9_relat_1(B_88, A_89)) | ~r1_tarski(k7_relat_1(B_86, A_87), k7_relat_1(B_88, A_89)) | ~v1_relat_1(k7_relat_1(B_88, A_89)) | ~v1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_88) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_22, c_266])).
% 2.81/1.39  tff(c_206, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.39  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.39  tff(c_220, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_206, c_28])).
% 2.81/1.39  tff(c_257, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.81/1.39  tff(c_302, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_257])).
% 2.81/1.39  tff(c_308, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_302])).
% 2.81/1.39  tff(c_310, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_308])).
% 2.81/1.39  tff(c_313, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_310])).
% 2.81/1.39  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_313])).
% 2.81/1.39  tff(c_318, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_308])).
% 2.81/1.39  tff(c_320, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_318])).
% 2.81/1.39  tff(c_323, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_320])).
% 2.81/1.39  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2, c_323])).
% 2.81/1.39  tff(c_328, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_318])).
% 2.81/1.39  tff(c_332, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_328])).
% 2.81/1.39  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_332])).
% 2.81/1.39  tff(c_337, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_220])).
% 2.81/1.39  tff(c_405, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_402, c_337])).
% 2.81/1.39  tff(c_411, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_405])).
% 2.81/1.39  tff(c_413, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_411])).
% 2.81/1.39  tff(c_416, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_413])).
% 2.81/1.39  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_416])).
% 2.81/1.39  tff(c_421, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_411])).
% 2.81/1.39  tff(c_423, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_421])).
% 2.81/1.39  tff(c_426, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_423])).
% 2.81/1.39  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_134, c_426])).
% 2.81/1.39  tff(c_431, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_421])).
% 2.81/1.39  tff(c_435, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_431])).
% 2.81/1.39  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_435])).
% 2.81/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  Inference rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Ref     : 0
% 2.81/1.39  #Sup     : 89
% 2.81/1.39  #Fact    : 0
% 2.81/1.39  #Define  : 0
% 2.81/1.39  #Split   : 6
% 2.81/1.39  #Chain   : 0
% 2.81/1.39  #Close   : 0
% 2.81/1.39  
% 2.81/1.39  Ordering : KBO
% 2.81/1.39  
% 2.81/1.39  Simplification rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Subsume      : 13
% 2.81/1.39  #Demod        : 16
% 2.81/1.39  #Tautology    : 31
% 2.81/1.39  #SimpNegUnit  : 0
% 2.81/1.39  #BackRed      : 0
% 2.81/1.39  
% 2.81/1.39  #Partial instantiations: 0
% 2.81/1.39  #Strategies tried      : 1
% 2.81/1.39  
% 2.81/1.39  Timing (in seconds)
% 2.81/1.39  ----------------------
% 2.81/1.39  Preprocessing        : 0.30
% 2.81/1.39  Parsing              : 0.16
% 2.81/1.40  CNF conversion       : 0.02
% 2.81/1.40  Main loop            : 0.29
% 2.81/1.40  Inferencing          : 0.12
% 2.81/1.40  Reduction            : 0.09
% 2.81/1.40  Demodulation         : 0.07
% 2.81/1.40  BG Simplification    : 0.01
% 2.81/1.40  Subsumption          : 0.06
% 2.81/1.40  Abstraction          : 0.01
% 2.81/1.40  MUC search           : 0.00
% 2.81/1.40  Cooper               : 0.00
% 2.81/1.40  Total                : 0.63
% 2.81/1.40  Index Insertion      : 0.00
% 2.81/1.40  Index Deletion       : 0.00
% 2.81/1.40  Index Matching       : 0.00
% 2.81/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
