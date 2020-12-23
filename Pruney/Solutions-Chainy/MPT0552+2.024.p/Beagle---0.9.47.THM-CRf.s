%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 185 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 386 expanded)
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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(B_36,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [B_36,A_35] : k3_xboole_0(B_36,A_35) = k3_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_10])).

tff(c_208,plain,(
    ! [C_53,A_54,B_55] :
      ( k3_xboole_0(k7_relat_1(C_53,A_54),k7_relat_1(C_53,B_55)) = k7_relat_1(C_53,k3_xboole_0(A_54,B_55))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5172,plain,(
    ! [C_243,A_244,B_245] :
      ( r1_tarski(k7_relat_1(C_243,k3_xboole_0(A_244,B_245)),k7_relat_1(C_243,A_244))
      | ~ v1_relat_1(C_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_2])).

tff(c_5185,plain,(
    ! [C_243,B_36,A_35] :
      ( r1_tarski(k7_relat_1(C_243,k3_xboole_0(B_36,A_35)),k7_relat_1(C_243,A_35))
      | ~ v1_relat_1(C_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_5172])).

tff(c_18,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k2_relat_1(A_46),k2_relat_1(B_47))
      | ~ r1_tarski(A_46,B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5441,plain,(
    ! [A_258,B_259,A_260] :
      ( r1_tarski(k2_relat_1(A_258),k9_relat_1(B_259,A_260))
      | ~ r1_tarski(A_258,k7_relat_1(B_259,A_260))
      | ~ v1_relat_1(k7_relat_1(B_259,A_260))
      | ~ v1_relat_1(A_258)
      | ~ v1_relat_1(B_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_179])).

tff(c_9684,plain,(
    ! [B_422,A_423,B_424,A_425] :
      ( r1_tarski(k9_relat_1(B_422,A_423),k9_relat_1(B_424,A_425))
      | ~ r1_tarski(k7_relat_1(B_422,A_423),k7_relat_1(B_424,A_425))
      | ~ v1_relat_1(k7_relat_1(B_424,A_425))
      | ~ v1_relat_1(k7_relat_1(B_422,A_423))
      | ~ v1_relat_1(B_424)
      | ~ v1_relat_1(B_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5441])).

tff(c_226,plain,(
    ! [C_53,A_54,B_55] :
      ( r1_tarski(k7_relat_1(C_53,k3_xboole_0(A_54,B_55)),k7_relat_1(C_53,A_54))
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_2])).

tff(c_644,plain,(
    ! [B_82,A_83,B_84] :
      ( r1_tarski(k9_relat_1(B_82,A_83),k2_relat_1(B_84))
      | ~ r1_tarski(k7_relat_1(B_82,A_83),B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(k7_relat_1(B_82,A_83))
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_179])).

tff(c_5076,plain,(
    ! [B_239,A_240,B_241,A_242] :
      ( r1_tarski(k9_relat_1(B_239,A_240),k9_relat_1(B_241,A_242))
      | ~ r1_tarski(k7_relat_1(B_239,A_240),k7_relat_1(B_241,A_242))
      | ~ v1_relat_1(k7_relat_1(B_241,A_242))
      | ~ v1_relat_1(k7_relat_1(B_239,A_240))
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(B_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_644])).

tff(c_168,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,k3_xboole_0(B_44,C_45))
      | ~ r1_tarski(A_43,C_45)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_178,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_168,c_24])).

tff(c_244,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_5079,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5076,c_244])).

tff(c_5142,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5079])).

tff(c_5143,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5142])).

tff(c_5146,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_5143])).

tff(c_5150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5146])).

tff(c_5151,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5142])).

tff(c_5153,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5151])).

tff(c_5156,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_5153])).

tff(c_5160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5156])).

tff(c_5161,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5151])).

tff(c_5165,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_5161])).

tff(c_5169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5165])).

tff(c_5170,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_9687,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9684,c_5170])).

tff(c_9750,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9687])).

tff(c_9751,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9750])).

tff(c_9754,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_9751])).

tff(c_9758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9754])).

tff(c_9759,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_9750])).

tff(c_9761,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9759])).

tff(c_9764,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5185,c_9761])).

tff(c_9768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9764])).

tff(c_9769,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_9759])).

tff(c_9773,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_9769])).

tff(c_9777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/3.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.15  
% 9.58/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.15  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 9.58/3.15  
% 9.58/3.15  %Foreground sorts:
% 9.58/3.15  
% 9.58/3.15  
% 9.58/3.15  %Background operators:
% 9.58/3.15  
% 9.58/3.15  
% 9.58/3.15  %Foreground operators:
% 9.58/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/3.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.58/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.58/3.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.58/3.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.58/3.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.58/3.15  tff('#skF_2', type, '#skF_2': $i).
% 9.58/3.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.58/3.15  tff('#skF_3', type, '#skF_3': $i).
% 9.58/3.15  tff('#skF_1', type, '#skF_1': $i).
% 9.58/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/3.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.58/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/3.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.58/3.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.58/3.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.58/3.15  
% 9.58/3.16  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 9.58/3.16  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.58/3.16  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.58/3.16  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.58/3.16  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 9.58/3.16  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.58/3.16  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.58/3.16  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.58/3.16  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 9.58/3.16  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.58/3.16  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.58/3.16  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.58/3.16  tff(c_62, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.58/3.16  tff(c_86, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(B_36, A_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 9.58/3.16  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.58/3.16  tff(c_92, plain, (![B_36, A_35]: (k3_xboole_0(B_36, A_35)=k3_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_86, c_10])).
% 9.58/3.16  tff(c_208, plain, (![C_53, A_54, B_55]: (k3_xboole_0(k7_relat_1(C_53, A_54), k7_relat_1(C_53, B_55))=k7_relat_1(C_53, k3_xboole_0(A_54, B_55)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.58/3.16  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.58/3.16  tff(c_5172, plain, (![C_243, A_244, B_245]: (r1_tarski(k7_relat_1(C_243, k3_xboole_0(A_244, B_245)), k7_relat_1(C_243, A_244)) | ~v1_relat_1(C_243))), inference(superposition, [status(thm), theory('equality')], [c_208, c_2])).
% 9.58/3.16  tff(c_5185, plain, (![C_243, B_36, A_35]: (r1_tarski(k7_relat_1(C_243, k3_xboole_0(B_36, A_35)), k7_relat_1(C_243, A_35)) | ~v1_relat_1(C_243))), inference(superposition, [status(thm), theory('equality')], [c_92, c_5172])).
% 9.58/3.16  tff(c_18, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.58/3.16  tff(c_179, plain, (![A_46, B_47]: (r1_tarski(k2_relat_1(A_46), k2_relat_1(B_47)) | ~r1_tarski(A_46, B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.58/3.16  tff(c_5441, plain, (![A_258, B_259, A_260]: (r1_tarski(k2_relat_1(A_258), k9_relat_1(B_259, A_260)) | ~r1_tarski(A_258, k7_relat_1(B_259, A_260)) | ~v1_relat_1(k7_relat_1(B_259, A_260)) | ~v1_relat_1(A_258) | ~v1_relat_1(B_259))), inference(superposition, [status(thm), theory('equality')], [c_18, c_179])).
% 9.58/3.16  tff(c_9684, plain, (![B_422, A_423, B_424, A_425]: (r1_tarski(k9_relat_1(B_422, A_423), k9_relat_1(B_424, A_425)) | ~r1_tarski(k7_relat_1(B_422, A_423), k7_relat_1(B_424, A_425)) | ~v1_relat_1(k7_relat_1(B_424, A_425)) | ~v1_relat_1(k7_relat_1(B_422, A_423)) | ~v1_relat_1(B_424) | ~v1_relat_1(B_422))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5441])).
% 9.58/3.16  tff(c_226, plain, (![C_53, A_54, B_55]: (r1_tarski(k7_relat_1(C_53, k3_xboole_0(A_54, B_55)), k7_relat_1(C_53, A_54)) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_208, c_2])).
% 9.58/3.16  tff(c_644, plain, (![B_82, A_83, B_84]: (r1_tarski(k9_relat_1(B_82, A_83), k2_relat_1(B_84)) | ~r1_tarski(k7_relat_1(B_82, A_83), B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(k7_relat_1(B_82, A_83)) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_18, c_179])).
% 9.58/3.16  tff(c_5076, plain, (![B_239, A_240, B_241, A_242]: (r1_tarski(k9_relat_1(B_239, A_240), k9_relat_1(B_241, A_242)) | ~r1_tarski(k7_relat_1(B_239, A_240), k7_relat_1(B_241, A_242)) | ~v1_relat_1(k7_relat_1(B_241, A_242)) | ~v1_relat_1(k7_relat_1(B_239, A_240)) | ~v1_relat_1(B_239) | ~v1_relat_1(B_241))), inference(superposition, [status(thm), theory('equality')], [c_18, c_644])).
% 9.58/3.16  tff(c_168, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, k3_xboole_0(B_44, C_45)) | ~r1_tarski(A_43, C_45) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.58/3.16  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.58/3.16  tff(c_178, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_168, c_24])).
% 9.58/3.16  tff(c_244, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_178])).
% 9.58/3.16  tff(c_5079, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5076, c_244])).
% 9.58/3.16  tff(c_5142, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5079])).
% 9.58/3.16  tff(c_5143, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5142])).
% 9.58/3.16  tff(c_5146, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_5143])).
% 9.58/3.16  tff(c_5150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_5146])).
% 9.58/3.16  tff(c_5151, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_5142])).
% 9.58/3.16  tff(c_5153, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5151])).
% 9.58/3.16  tff(c_5156, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_226, c_5153])).
% 9.58/3.16  tff(c_5160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_5156])).
% 9.58/3.16  tff(c_5161, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_5151])).
% 9.58/3.16  tff(c_5165, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_5161])).
% 9.58/3.16  tff(c_5169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_5165])).
% 9.58/3.16  tff(c_5170, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_178])).
% 9.58/3.16  tff(c_9687, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9684, c_5170])).
% 9.58/3.16  tff(c_9750, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9687])).
% 9.58/3.16  tff(c_9751, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_9750])).
% 9.58/3.16  tff(c_9754, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_9751])).
% 9.58/3.16  tff(c_9758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_9754])).
% 9.58/3.16  tff(c_9759, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_9750])).
% 9.58/3.16  tff(c_9761, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_9759])).
% 9.58/3.16  tff(c_9764, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5185, c_9761])).
% 9.58/3.16  tff(c_9768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_9764])).
% 9.58/3.16  tff(c_9769, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_9759])).
% 9.58/3.16  tff(c_9773, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_9769])).
% 9.58/3.16  tff(c_9777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_9773])).
% 9.58/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.16  
% 9.58/3.16  Inference rules
% 9.58/3.16  ----------------------
% 9.58/3.16  #Ref     : 0
% 9.58/3.16  #Sup     : 2868
% 9.58/3.16  #Fact    : 0
% 9.58/3.16  #Define  : 0
% 9.58/3.16  #Split   : 5
% 9.58/3.16  #Chain   : 0
% 9.58/3.16  #Close   : 0
% 9.58/3.16  
% 9.58/3.16  Ordering : KBO
% 9.58/3.16  
% 9.58/3.16  Simplification rules
% 9.58/3.16  ----------------------
% 9.58/3.16  #Subsume      : 439
% 9.58/3.16  #Demod        : 14
% 9.58/3.16  #Tautology    : 160
% 9.58/3.16  #SimpNegUnit  : 0
% 9.58/3.16  #BackRed      : 0
% 9.58/3.16  
% 9.58/3.16  #Partial instantiations: 0
% 9.58/3.16  #Strategies tried      : 1
% 9.58/3.16  
% 9.58/3.16  Timing (in seconds)
% 9.58/3.16  ----------------------
% 9.58/3.17  Preprocessing        : 0.32
% 9.58/3.17  Parsing              : 0.17
% 9.58/3.17  CNF conversion       : 0.02
% 9.58/3.17  Main loop            : 2.03
% 9.58/3.17  Inferencing          : 0.69
% 9.58/3.17  Reduction            : 0.62
% 9.58/3.17  Demodulation         : 0.51
% 9.58/3.17  BG Simplification    : 0.14
% 9.58/3.17  Subsumption          : 0.47
% 9.58/3.17  Abstraction          : 0.11
% 9.58/3.17  MUC search           : 0.00
% 9.58/3.17  Cooper               : 0.00
% 9.58/3.17  Total                : 2.38
% 9.58/3.17  Index Insertion      : 0.00
% 9.58/3.17  Index Deletion       : 0.00
% 9.58/3.17  Index Matching       : 0.00
% 9.58/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
