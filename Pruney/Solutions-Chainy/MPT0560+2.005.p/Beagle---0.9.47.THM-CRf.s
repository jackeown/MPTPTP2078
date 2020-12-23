%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 10.21s
% Output     : CNFRefutation 10.42s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  121 ( 192 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_33,A_34] : k1_setfam_1(k2_tarski(B_33,A_34)) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_12,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ r1_tarski(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_654,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(k7_relat_1(B_76,A_77),A_77) = k7_relat_1(B_76,A_77)
      | ~ v1_relat_1(k7_relat_1(B_76,A_77))
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_667,plain,(
    ! [A_10,B_11] :
      ( k7_relat_1(k7_relat_1(A_10,B_11),B_11) = k7_relat_1(A_10,B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_654])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_154,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,'#skF_3')
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_154])).

tff(c_173,plain,(
    ! [B_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_164])).

tff(c_942,plain,(
    ! [B_87] :
      ( k7_relat_1(k7_relat_1(B_87,'#skF_2'),'#skF_3') = k7_relat_1(B_87,'#skF_2')
      | ~ v1_relat_1(k7_relat_1(B_87,'#skF_2'))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_173,c_203])).

tff(c_960,plain,(
    ! [A_88] :
      ( k7_relat_1(k7_relat_1(A_88,'#skF_2'),'#skF_3') = k7_relat_1(A_88,'#skF_2')
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_14,c_942])).

tff(c_3594,plain,(
    ! [A_182] :
      ( k7_relat_1(k7_relat_1(A_182,'#skF_2'),'#skF_2') = k7_relat_1(k7_relat_1(A_182,'#skF_2'),'#skF_3')
      | ~ v1_relat_1(k7_relat_1(A_182,'#skF_2'))
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_960])).

tff(c_3616,plain,(
    ! [A_183] :
      ( k7_relat_1(k7_relat_1(A_183,'#skF_2'),'#skF_2') = k7_relat_1(k7_relat_1(A_183,'#skF_2'),'#skF_3')
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_14,c_3594])).

tff(c_16,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k7_relat_1(C_14,k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3773,plain,(
    ! [A_184] :
      ( k7_relat_1(k7_relat_1(A_184,'#skF_2'),'#skF_3') = k7_relat_1(A_184,k3_xboole_0('#skF_2','#skF_2'))
      | ~ v1_relat_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3616,c_16])).

tff(c_3829,plain,(
    ! [A_184] :
      ( k7_relat_1(A_184,k3_xboole_0('#skF_2','#skF_2')) = k7_relat_1(A_184,k3_xboole_0('#skF_2','#skF_3'))
      | ~ v1_relat_1(A_184)
      | ~ v1_relat_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3773,c_16])).

tff(c_5325,plain,(
    ! [A_210] :
      ( k7_relat_1(A_210,k3_xboole_0('#skF_2','#skF_2')) = k7_relat_1(A_210,k3_xboole_0('#skF_3','#skF_2'))
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3829])).

tff(c_305,plain,(
    ! [C_60,A_61,B_62] :
      ( k7_relat_1(k7_relat_1(C_60,A_61),B_62) = k7_relat_1(C_60,A_61)
      | ~ r1_tarski(A_61,B_62)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1097,plain,(
    ! [C_90,A_91,B_92] :
      ( k7_relat_1(C_90,k3_xboole_0(A_91,B_92)) = k7_relat_1(C_90,A_91)
      | ~ r1_tarski(A_91,B_92)
      | ~ v1_relat_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_1195,plain,(
    ! [C_90,A_34,B_33] :
      ( k7_relat_1(C_90,k3_xboole_0(A_34,B_33)) = k7_relat_1(C_90,B_33)
      | ~ r1_tarski(B_33,A_34)
      | ~ v1_relat_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1097])).

tff(c_5382,plain,(
    ! [A_210] :
      ( k7_relat_1(A_210,k3_xboole_0('#skF_3','#skF_2')) = k7_relat_1(A_210,'#skF_2')
      | ~ r1_tarski('#skF_2','#skF_2')
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5325,c_1195])).

tff(c_5936,plain,(
    ! [A_215] :
      ( k7_relat_1(A_215,k3_xboole_0('#skF_3','#skF_2')) = k7_relat_1(A_215,'#skF_2')
      | ~ v1_relat_1(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5382])).

tff(c_6058,plain,(
    ! [A_215] :
      ( k9_relat_1(A_215,k3_xboole_0('#skF_3','#skF_2')) = k2_relat_1(k7_relat_1(A_215,'#skF_2'))
      | ~ v1_relat_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5936,c_20])).

tff(c_259,plain,(
    ! [C_57,A_58,B_59] :
      ( k7_relat_1(k7_relat_1(C_57,A_58),B_59) = k7_relat_1(C_57,k3_xboole_0(A_58,B_59))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2290,plain,(
    ! [C_140,A_141,B_142] :
      ( k2_relat_1(k7_relat_1(C_140,k3_xboole_0(A_141,B_142))) = k9_relat_1(k7_relat_1(C_140,A_141),B_142)
      | ~ v1_relat_1(k7_relat_1(C_140,A_141))
      | ~ v1_relat_1(C_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_20])).

tff(c_13269,plain,(
    ! [C_338,A_339,B_340] :
      ( k9_relat_1(k7_relat_1(C_338,A_339),B_340) = k9_relat_1(C_338,k3_xboole_0(A_339,B_340))
      | ~ v1_relat_1(C_338)
      | ~ v1_relat_1(k7_relat_1(C_338,A_339))
      | ~ v1_relat_1(C_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2290,c_20])).

tff(c_13367,plain,(
    ! [A_341,B_342,B_343] :
      ( k9_relat_1(k7_relat_1(A_341,B_342),B_343) = k9_relat_1(A_341,k3_xboole_0(B_342,B_343))
      | ~ v1_relat_1(A_341) ) ),
    inference(resolution,[status(thm)],[c_14,c_13269])).

tff(c_26,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_13424,plain,
    ( k9_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13367,c_26])).

tff(c_13594,plain,(
    k9_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_13424])).

tff(c_13602,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6058,c_13594])).

tff(c_13606,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_13602])).

tff(c_13609,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_13606])).

tff(c_13613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_13609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.21/3.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/3.64  
% 10.30/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/3.64  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 10.30/3.64  
% 10.30/3.64  %Foreground sorts:
% 10.30/3.64  
% 10.30/3.64  
% 10.30/3.64  %Background operators:
% 10.30/3.64  
% 10.30/3.64  
% 10.30/3.64  %Foreground operators:
% 10.30/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.30/3.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.30/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.30/3.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.30/3.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.30/3.64  tff('#skF_2', type, '#skF_2': $i).
% 10.30/3.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.30/3.64  tff('#skF_3', type, '#skF_3': $i).
% 10.30/3.64  tff('#skF_1', type, '#skF_1': $i).
% 10.30/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.30/3.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.30/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.30/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.30/3.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.30/3.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.30/3.64  
% 10.42/3.67  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 10.42/3.67  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 10.42/3.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.42/3.67  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.42/3.67  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.42/3.67  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 10.42/3.67  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 10.42/3.67  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 10.42/3.67  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.42/3.67  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 10.42/3.67  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 10.42/3.67  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.42/3.67  tff(c_20, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.42/3.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.42/3.67  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.42/3.67  tff(c_67, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.42/3.67  tff(c_82, plain, (![B_33, A_34]: (k1_setfam_1(k2_tarski(B_33, A_34))=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 10.42/3.67  tff(c_12, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.42/3.67  tff(c_88, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 10.42/3.67  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.42/3.67  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.42/3.67  tff(c_203, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~r1_tarski(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.42/3.67  tff(c_654, plain, (![B_76, A_77]: (k7_relat_1(k7_relat_1(B_76, A_77), A_77)=k7_relat_1(B_76, A_77) | ~v1_relat_1(k7_relat_1(B_76, A_77)) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_22, c_203])).
% 10.42/3.67  tff(c_667, plain, (![A_10, B_11]: (k7_relat_1(k7_relat_1(A_10, B_11), B_11)=k7_relat_1(A_10, B_11) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_14, c_654])).
% 10.42/3.67  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.42/3.67  tff(c_154, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.42/3.67  tff(c_164, plain, (![A_44]: (r1_tarski(A_44, '#skF_3') | ~r1_tarski(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_154])).
% 10.42/3.67  tff(c_173, plain, (![B_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, '#skF_2')), '#skF_3') | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_22, c_164])).
% 10.42/3.67  tff(c_942, plain, (![B_87]: (k7_relat_1(k7_relat_1(B_87, '#skF_2'), '#skF_3')=k7_relat_1(B_87, '#skF_2') | ~v1_relat_1(k7_relat_1(B_87, '#skF_2')) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_173, c_203])).
% 10.42/3.67  tff(c_960, plain, (![A_88]: (k7_relat_1(k7_relat_1(A_88, '#skF_2'), '#skF_3')=k7_relat_1(A_88, '#skF_2') | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_14, c_942])).
% 10.42/3.67  tff(c_3594, plain, (![A_182]: (k7_relat_1(k7_relat_1(A_182, '#skF_2'), '#skF_2')=k7_relat_1(k7_relat_1(A_182, '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1(A_182, '#skF_2')) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_667, c_960])).
% 10.42/3.67  tff(c_3616, plain, (![A_183]: (k7_relat_1(k7_relat_1(A_183, '#skF_2'), '#skF_2')=k7_relat_1(k7_relat_1(A_183, '#skF_2'), '#skF_3') | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_14, c_3594])).
% 10.42/3.67  tff(c_16, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k7_relat_1(C_14, k3_xboole_0(A_12, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.42/3.67  tff(c_3773, plain, (![A_184]: (k7_relat_1(k7_relat_1(A_184, '#skF_2'), '#skF_3')=k7_relat_1(A_184, k3_xboole_0('#skF_2', '#skF_2')) | ~v1_relat_1(A_184) | ~v1_relat_1(A_184))), inference(superposition, [status(thm), theory('equality')], [c_3616, c_16])).
% 10.42/3.67  tff(c_3829, plain, (![A_184]: (k7_relat_1(A_184, k3_xboole_0('#skF_2', '#skF_2'))=k7_relat_1(A_184, k3_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1(A_184) | ~v1_relat_1(A_184) | ~v1_relat_1(A_184))), inference(superposition, [status(thm), theory('equality')], [c_3773, c_16])).
% 10.42/3.67  tff(c_5325, plain, (![A_210]: (k7_relat_1(A_210, k3_xboole_0('#skF_2', '#skF_2'))=k7_relat_1(A_210, k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1(A_210) | ~v1_relat_1(A_210) | ~v1_relat_1(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3829])).
% 10.42/3.67  tff(c_305, plain, (![C_60, A_61, B_62]: (k7_relat_1(k7_relat_1(C_60, A_61), B_62)=k7_relat_1(C_60, A_61) | ~r1_tarski(A_61, B_62) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.42/3.67  tff(c_1097, plain, (![C_90, A_91, B_92]: (k7_relat_1(C_90, k3_xboole_0(A_91, B_92))=k7_relat_1(C_90, A_91) | ~r1_tarski(A_91, B_92) | ~v1_relat_1(C_90) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_16, c_305])).
% 10.42/3.67  tff(c_1195, plain, (![C_90, A_34, B_33]: (k7_relat_1(C_90, k3_xboole_0(A_34, B_33))=k7_relat_1(C_90, B_33) | ~r1_tarski(B_33, A_34) | ~v1_relat_1(C_90) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1097])).
% 10.42/3.67  tff(c_5382, plain, (![A_210]: (k7_relat_1(A_210, k3_xboole_0('#skF_3', '#skF_2'))=k7_relat_1(A_210, '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1(A_210) | ~v1_relat_1(A_210) | ~v1_relat_1(A_210) | ~v1_relat_1(A_210) | ~v1_relat_1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_5325, c_1195])).
% 10.42/3.67  tff(c_5936, plain, (![A_215]: (k7_relat_1(A_215, k3_xboole_0('#skF_3', '#skF_2'))=k7_relat_1(A_215, '#skF_2') | ~v1_relat_1(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5382])).
% 10.42/3.67  tff(c_6058, plain, (![A_215]: (k9_relat_1(A_215, k3_xboole_0('#skF_3', '#skF_2'))=k2_relat_1(k7_relat_1(A_215, '#skF_2')) | ~v1_relat_1(A_215) | ~v1_relat_1(A_215))), inference(superposition, [status(thm), theory('equality')], [c_5936, c_20])).
% 10.42/3.67  tff(c_259, plain, (![C_57, A_58, B_59]: (k7_relat_1(k7_relat_1(C_57, A_58), B_59)=k7_relat_1(C_57, k3_xboole_0(A_58, B_59)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.42/3.67  tff(c_2290, plain, (![C_140, A_141, B_142]: (k2_relat_1(k7_relat_1(C_140, k3_xboole_0(A_141, B_142)))=k9_relat_1(k7_relat_1(C_140, A_141), B_142) | ~v1_relat_1(k7_relat_1(C_140, A_141)) | ~v1_relat_1(C_140))), inference(superposition, [status(thm), theory('equality')], [c_259, c_20])).
% 10.42/3.67  tff(c_13269, plain, (![C_338, A_339, B_340]: (k9_relat_1(k7_relat_1(C_338, A_339), B_340)=k9_relat_1(C_338, k3_xboole_0(A_339, B_340)) | ~v1_relat_1(C_338) | ~v1_relat_1(k7_relat_1(C_338, A_339)) | ~v1_relat_1(C_338))), inference(superposition, [status(thm), theory('equality')], [c_2290, c_20])).
% 10.42/3.67  tff(c_13367, plain, (![A_341, B_342, B_343]: (k9_relat_1(k7_relat_1(A_341, B_342), B_343)=k9_relat_1(A_341, k3_xboole_0(B_342, B_343)) | ~v1_relat_1(A_341))), inference(resolution, [status(thm)], [c_14, c_13269])).
% 10.42/3.67  tff(c_26, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.42/3.67  tff(c_13424, plain, (k9_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13367, c_26])).
% 10.42/3.67  tff(c_13594, plain, (k9_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_13424])).
% 10.42/3.67  tff(c_13602, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6058, c_13594])).
% 10.42/3.67  tff(c_13606, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_13602])).
% 10.42/3.67  tff(c_13609, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_13606])).
% 10.42/3.67  tff(c_13613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_13609])).
% 10.42/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.42/3.67  
% 10.42/3.67  Inference rules
% 10.42/3.67  ----------------------
% 10.42/3.67  #Ref     : 0
% 10.42/3.67  #Sup     : 3877
% 10.42/3.67  #Fact    : 0
% 10.42/3.67  #Define  : 0
% 10.42/3.67  #Split   : 1
% 10.42/3.67  #Chain   : 0
% 10.42/3.67  #Close   : 0
% 10.42/3.67  
% 10.42/3.67  Ordering : KBO
% 10.42/3.67  
% 10.42/3.67  Simplification rules
% 10.42/3.67  ----------------------
% 10.42/3.67  #Subsume      : 920
% 10.42/3.67  #Demod        : 226
% 10.42/3.67  #Tautology    : 304
% 10.42/3.67  #SimpNegUnit  : 0
% 10.42/3.67  #BackRed      : 0
% 10.42/3.67  
% 10.42/3.67  #Partial instantiations: 0
% 10.42/3.67  #Strategies tried      : 1
% 10.42/3.67  
% 10.42/3.67  Timing (in seconds)
% 10.42/3.67  ----------------------
% 10.42/3.67  Preprocessing        : 0.31
% 10.42/3.67  Parsing              : 0.17
% 10.42/3.67  CNF conversion       : 0.02
% 10.42/3.67  Main loop            : 2.57
% 10.42/3.68  Inferencing          : 0.72
% 10.42/3.68  Reduction            : 0.69
% 10.42/3.68  Demodulation         : 0.52
% 10.42/3.68  BG Simplification    : 0.14
% 10.42/3.68  Subsumption          : 0.88
% 10.42/3.68  Abstraction          : 0.12
% 10.42/3.68  MUC search           : 0.00
% 10.42/3.68  Cooper               : 0.00
% 10.42/3.68  Total                : 2.93
% 10.42/3.68  Index Insertion      : 0.00
% 10.42/3.68  Index Deletion       : 0.00
% 10.42/3.68  Index Matching       : 0.00
% 10.42/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
