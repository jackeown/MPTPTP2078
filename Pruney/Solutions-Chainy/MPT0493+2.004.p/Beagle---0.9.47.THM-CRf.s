%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:36 EST 2020

% Result     : Theorem 10.33s
% Output     : CNFRefutation 10.33s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 161 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  106 ( 281 expanded)
%              Number of equality atoms :   41 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_36,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,A_38)
      | ~ r2_hidden(D_37,k4_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1555,plain,(
    ! [A_128,B_129,B_130] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_128,B_129),B_130),A_128)
      | r1_tarski(k4_xboole_0(A_128,B_129),B_130) ) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1624,plain,(
    ! [A_128,B_129] : r1_tarski(k4_xboole_0(A_128,B_129),A_128) ),
    inference(resolution,[status(thm)],[c_1555,c_4])).

tff(c_38,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_240,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1281,plain,(
    ! [A_109,B_110,B_111] :
      ( r2_hidden('#skF_1'(A_109,B_110),B_111)
      | ~ r1_tarski(A_109,B_111)
      | r1_tarski(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18227,plain,(
    ! [A_506,B_507,B_508,B_509] :
      ( r2_hidden('#skF_1'(A_506,B_507),B_508)
      | ~ r1_tarski(B_509,B_508)
      | ~ r1_tarski(A_506,B_509)
      | r1_tarski(A_506,B_507) ) ),
    inference(resolution,[status(thm)],[c_1281,c_2])).

tff(c_18294,plain,(
    ! [A_510,B_511] :
      ( r2_hidden('#skF_1'(A_510,B_511),k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_510,'#skF_4')
      | r1_tarski(A_510,B_511) ) ),
    inference(resolution,[status(thm)],[c_38,c_18227])).

tff(c_18315,plain,(
    ! [A_512] :
      ( ~ r1_tarski(A_512,'#skF_4')
      | r1_tarski(A_512,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_18294,c_4])).

tff(c_613,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_2'(A_84,B_85,C_86),A_84)
      | r2_hidden('#skF_3'(A_84,B_85,C_86),C_86)
      | k4_xboole_0(A_84,B_85) = C_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_692,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_3'(A_84,B_85,A_84),A_84)
      | k4_xboole_0(A_84,B_85) = A_84 ) ),
    inference(resolution,[status(thm)],[c_613,c_20])).

tff(c_713,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_3'(A_87,B_88,A_87),A_87)
      | k4_xboole_0(A_87,B_88) = A_87 ) ),
    inference(resolution,[status(thm)],[c_613,c_20])).

tff(c_154,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,(
    ! [D_30,A_12] :
      ( ~ r2_hidden(D_30,k1_xboole_0)
      | ~ r2_hidden(D_30,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_807,plain,(
    ! [B_91,A_92] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_91,k1_xboole_0),A_92)
      | k4_xboole_0(k1_xboole_0,B_91) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_713,c_157])).

tff(c_932,plain,(
    ! [B_96] : k4_xboole_0(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_692,c_807])).

tff(c_28,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_959,plain,(
    ! [B_96] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_28])).

tff(c_1017,plain,(
    ! [B_97] : k3_xboole_0(k1_xboole_0,B_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_959])).

tff(c_30,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,(
    ! [B_26,A_27] : k1_setfam_1(k2_tarski(B_26,A_27)) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_83])).

tff(c_32,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_32])).

tff(c_1046,plain,(
    ! [B_97] : k3_xboole_0(B_97,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_104])).

tff(c_179,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_179])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_627,plain,(
    ! [A_84,C_86] :
      ( r2_hidden('#skF_3'(A_84,A_84,C_86),C_86)
      | k4_xboole_0(A_84,A_84) = C_86 ) ),
    inference(resolution,[status(thm)],[c_613,c_22])).

tff(c_695,plain,(
    ! [A_84,C_86] :
      ( r2_hidden('#skF_3'(A_84,A_84,C_86),C_86)
      | k3_xboole_0(A_84,k1_xboole_0) = C_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_627])).

tff(c_1342,plain,(
    ! [A_113,C_114] :
      ( r2_hidden('#skF_3'(A_113,A_113,C_114),C_114)
      | k1_xboole_0 = C_114 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_695])).

tff(c_1376,plain,(
    ! [A_113,C_114,B_2] :
      ( r2_hidden('#skF_3'(A_113,A_113,C_114),B_2)
      | ~ r1_tarski(C_114,B_2)
      | k1_xboole_0 = C_114 ) ),
    inference(resolution,[status(thm)],[c_1342,c_2])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4856,plain,(
    ! [A_243,A_244,B_245] :
      ( ~ r2_hidden('#skF_3'(A_243,A_243,k4_xboole_0(A_244,B_245)),B_245)
      | k4_xboole_0(A_244,B_245) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1342,c_10])).

tff(c_4911,plain,(
    ! [A_244,B_2] :
      ( ~ r1_tarski(k4_xboole_0(A_244,B_2),B_2)
      | k4_xboole_0(A_244,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1376,c_4856])).

tff(c_18332,plain,(
    ! [A_513] :
      ( k4_xboole_0(A_513,k1_relat_1('#skF_5')) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_513,k1_relat_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18315,c_4911])).

tff(c_18345,plain,(
    k4_xboole_0('#skF_4',k1_relat_1('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1624,c_18332])).

tff(c_18662,plain,(
    k3_xboole_0('#skF_4',k1_relat_1('#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18345,c_28])).

tff(c_18758,plain,(
    k3_xboole_0('#skF_4',k1_relat_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18662])).

tff(c_305,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),A_56) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_332,plain,(
    ! [B_26,B_55] :
      ( k3_xboole_0(B_26,k1_relat_1(B_55)) = k1_relat_1(k7_relat_1(B_55,B_26))
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_305])).

tff(c_18926,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18758,c_332])).

tff(c_18993,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18926])).

tff(c_18995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_18993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:12:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.33/3.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.33/4.00  
% 10.33/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.33/4.00  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.33/4.00  
% 10.33/4.00  %Foreground sorts:
% 10.33/4.00  
% 10.33/4.00  
% 10.33/4.00  %Background operators:
% 10.33/4.00  
% 10.33/4.00  
% 10.33/4.00  %Foreground operators:
% 10.33/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.33/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.33/4.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.33/4.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.33/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.33/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.33/4.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.33/4.00  tff('#skF_5', type, '#skF_5': $i).
% 10.33/4.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.33/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.33/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.33/4.00  tff('#skF_4', type, '#skF_4': $i).
% 10.33/4.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.33/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.33/4.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.33/4.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.33/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.33/4.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.33/4.00  
% 10.33/4.02  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 10.33/4.02  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.33/4.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.33/4.02  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.33/4.02  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.33/4.02  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.33/4.02  tff(f_50, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.33/4.02  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 10.33/4.02  tff(c_36, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.33/4.02  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.33/4.02  tff(c_26, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.33/4.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.33/4.02  tff(c_170, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, A_38) | ~r2_hidden(D_37, k4_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.33/4.02  tff(c_1555, plain, (![A_128, B_129, B_130]: (r2_hidden('#skF_1'(k4_xboole_0(A_128, B_129), B_130), A_128) | r1_tarski(k4_xboole_0(A_128, B_129), B_130))), inference(resolution, [status(thm)], [c_6, c_170])).
% 10.33/4.02  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.33/4.02  tff(c_1624, plain, (![A_128, B_129]: (r1_tarski(k4_xboole_0(A_128, B_129), A_128))), inference(resolution, [status(thm)], [c_1555, c_4])).
% 10.33/4.02  tff(c_38, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.33/4.02  tff(c_240, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.33/4.02  tff(c_1281, plain, (![A_109, B_110, B_111]: (r2_hidden('#skF_1'(A_109, B_110), B_111) | ~r1_tarski(A_109, B_111) | r1_tarski(A_109, B_110))), inference(resolution, [status(thm)], [c_6, c_240])).
% 10.33/4.02  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.33/4.02  tff(c_18227, plain, (![A_506, B_507, B_508, B_509]: (r2_hidden('#skF_1'(A_506, B_507), B_508) | ~r1_tarski(B_509, B_508) | ~r1_tarski(A_506, B_509) | r1_tarski(A_506, B_507))), inference(resolution, [status(thm)], [c_1281, c_2])).
% 10.33/4.02  tff(c_18294, plain, (![A_510, B_511]: (r2_hidden('#skF_1'(A_510, B_511), k1_relat_1('#skF_5')) | ~r1_tarski(A_510, '#skF_4') | r1_tarski(A_510, B_511))), inference(resolution, [status(thm)], [c_38, c_18227])).
% 10.33/4.02  tff(c_18315, plain, (![A_512]: (~r1_tarski(A_512, '#skF_4') | r1_tarski(A_512, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_18294, c_4])).
% 10.33/4.02  tff(c_613, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_2'(A_84, B_85, C_86), A_84) | r2_hidden('#skF_3'(A_84, B_85, C_86), C_86) | k4_xboole_0(A_84, B_85)=C_86)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.33/4.02  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.33/4.02  tff(c_692, plain, (![A_84, B_85]: (r2_hidden('#skF_3'(A_84, B_85, A_84), A_84) | k4_xboole_0(A_84, B_85)=A_84)), inference(resolution, [status(thm)], [c_613, c_20])).
% 10.33/4.02  tff(c_713, plain, (![A_87, B_88]: (r2_hidden('#skF_3'(A_87, B_88, A_87), A_87) | k4_xboole_0(A_87, B_88)=A_87)), inference(resolution, [status(thm)], [c_613, c_20])).
% 10.33/4.02  tff(c_154, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.33/4.02  tff(c_157, plain, (![D_30, A_12]: (~r2_hidden(D_30, k1_xboole_0) | ~r2_hidden(D_30, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_154])).
% 10.33/4.02  tff(c_807, plain, (![B_91, A_92]: (~r2_hidden('#skF_3'(k1_xboole_0, B_91, k1_xboole_0), A_92) | k4_xboole_0(k1_xboole_0, B_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_713, c_157])).
% 10.33/4.02  tff(c_932, plain, (![B_96]: (k4_xboole_0(k1_xboole_0, B_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_692, c_807])).
% 10.33/4.02  tff(c_28, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.33/4.02  tff(c_959, plain, (![B_96]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_96))), inference(superposition, [status(thm), theory('equality')], [c_932, c_28])).
% 10.33/4.02  tff(c_1017, plain, (![B_97]: (k3_xboole_0(k1_xboole_0, B_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_959])).
% 10.33/4.02  tff(c_30, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.33/4.02  tff(c_83, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.33/4.02  tff(c_98, plain, (![B_26, A_27]: (k1_setfam_1(k2_tarski(B_26, A_27))=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_30, c_83])).
% 10.33/4.02  tff(c_32, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.33/4.02  tff(c_104, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_98, c_32])).
% 10.33/4.02  tff(c_1046, plain, (![B_97]: (k3_xboole_0(B_97, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1017, c_104])).
% 10.33/4.02  tff(c_179, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.33/4.02  tff(c_200, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_179])).
% 10.33/4.02  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.33/4.02  tff(c_627, plain, (![A_84, C_86]: (r2_hidden('#skF_3'(A_84, A_84, C_86), C_86) | k4_xboole_0(A_84, A_84)=C_86)), inference(resolution, [status(thm)], [c_613, c_22])).
% 10.33/4.02  tff(c_695, plain, (![A_84, C_86]: (r2_hidden('#skF_3'(A_84, A_84, C_86), C_86) | k3_xboole_0(A_84, k1_xboole_0)=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_627])).
% 10.33/4.02  tff(c_1342, plain, (![A_113, C_114]: (r2_hidden('#skF_3'(A_113, A_113, C_114), C_114) | k1_xboole_0=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_695])).
% 10.33/4.02  tff(c_1376, plain, (![A_113, C_114, B_2]: (r2_hidden('#skF_3'(A_113, A_113, C_114), B_2) | ~r1_tarski(C_114, B_2) | k1_xboole_0=C_114)), inference(resolution, [status(thm)], [c_1342, c_2])).
% 10.33/4.02  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.33/4.02  tff(c_4856, plain, (![A_243, A_244, B_245]: (~r2_hidden('#skF_3'(A_243, A_243, k4_xboole_0(A_244, B_245)), B_245) | k4_xboole_0(A_244, B_245)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1342, c_10])).
% 10.33/4.02  tff(c_4911, plain, (![A_244, B_2]: (~r1_tarski(k4_xboole_0(A_244, B_2), B_2) | k4_xboole_0(A_244, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1376, c_4856])).
% 10.33/4.02  tff(c_18332, plain, (![A_513]: (k4_xboole_0(A_513, k1_relat_1('#skF_5'))=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_513, k1_relat_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_18315, c_4911])).
% 10.33/4.02  tff(c_18345, plain, (k4_xboole_0('#skF_4', k1_relat_1('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1624, c_18332])).
% 10.33/4.02  tff(c_18662, plain, (k3_xboole_0('#skF_4', k1_relat_1('#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18345, c_28])).
% 10.33/4.02  tff(c_18758, plain, (k3_xboole_0('#skF_4', k1_relat_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18662])).
% 10.33/4.02  tff(c_305, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), A_56)=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.33/4.02  tff(c_332, plain, (![B_26, B_55]: (k3_xboole_0(B_26, k1_relat_1(B_55))=k1_relat_1(k7_relat_1(B_55, B_26)) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_104, c_305])).
% 10.33/4.02  tff(c_18926, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18758, c_332])).
% 10.33/4.02  tff(c_18993, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18926])).
% 10.33/4.02  tff(c_18995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_18993])).
% 10.33/4.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.33/4.02  
% 10.33/4.02  Inference rules
% 10.33/4.02  ----------------------
% 10.33/4.02  #Ref     : 0
% 10.33/4.02  #Sup     : 4663
% 10.33/4.02  #Fact    : 0
% 10.33/4.02  #Define  : 0
% 10.33/4.02  #Split   : 0
% 10.33/4.02  #Chain   : 0
% 10.33/4.02  #Close   : 0
% 10.33/4.02  
% 10.33/4.02  Ordering : KBO
% 10.33/4.02  
% 10.33/4.02  Simplification rules
% 10.33/4.02  ----------------------
% 10.33/4.02  #Subsume      : 856
% 10.33/4.02  #Demod        : 5310
% 10.33/4.02  #Tautology    : 1717
% 10.33/4.02  #SimpNegUnit  : 1
% 10.33/4.02  #BackRed      : 8
% 10.33/4.02  
% 10.33/4.02  #Partial instantiations: 0
% 10.33/4.02  #Strategies tried      : 1
% 10.33/4.02  
% 10.33/4.02  Timing (in seconds)
% 10.33/4.02  ----------------------
% 10.33/4.02  Preprocessing        : 0.32
% 10.33/4.02  Parsing              : 0.16
% 10.33/4.02  CNF conversion       : 0.02
% 10.33/4.02  Main loop            : 2.88
% 10.33/4.02  Inferencing          : 0.64
% 10.33/4.02  Reduction            : 1.29
% 10.33/4.02  Demodulation         : 1.11
% 10.33/4.02  BG Simplification    : 0.08
% 10.33/4.02  Subsumption          : 0.71
% 10.33/4.02  Abstraction          : 0.12
% 10.33/4.02  MUC search           : 0.00
% 10.33/4.02  Cooper               : 0.00
% 10.33/4.02  Total                : 3.23
% 10.33/4.02  Index Insertion      : 0.00
% 10.33/4.02  Index Deletion       : 0.00
% 10.33/4.02  Index Matching       : 0.00
% 10.33/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
