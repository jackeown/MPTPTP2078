%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 9.35s
% Output     : CNFRefutation 9.35s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 156 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  100 ( 279 expanded)
%              Number of equality atoms :   36 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_38,plain,(
    k2_relat_1(k8_relat_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1647,plain,(
    ! [A_147,B_148,B_149] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_147,B_148),B_149),A_147)
      | r1_tarski(k4_xboole_0(A_147,B_148),B_149) ) ),
    inference(resolution,[status(thm)],[c_175,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1721,plain,(
    ! [A_147,B_148] : r1_tarski(k4_xboole_0(A_147,B_148),A_147) ),
    inference(resolution,[status(thm)],[c_1647,c_4])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_247,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1377,plain,(
    ! [A_121,B_122,B_123] :
      ( r2_hidden('#skF_1'(A_121,B_122),B_123)
      | ~ r1_tarski(A_121,B_123)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17751,plain,(
    ! [A_505,B_506,B_507,B_508] :
      ( r2_hidden('#skF_1'(A_505,B_506),B_507)
      | ~ r1_tarski(B_508,B_507)
      | ~ r1_tarski(A_505,B_508)
      | r1_tarski(A_505,B_506) ) ),
    inference(resolution,[status(thm)],[c_1377,c_2])).

tff(c_17818,plain,(
    ! [A_509,B_510] :
      ( r2_hidden('#skF_1'(A_509,B_510),k2_relat_1('#skF_5'))
      | ~ r1_tarski(A_509,'#skF_4')
      | r1_tarski(A_509,B_510) ) ),
    inference(resolution,[status(thm)],[c_40,c_17751])).

tff(c_17839,plain,(
    ! [A_511] :
      ( ~ r1_tarski(A_511,'#skF_4')
      | r1_tarski(A_511,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_17818,c_4])).

tff(c_197,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_592,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden('#skF_2'(A_78,B_79,C_80),B_79)
      | r2_hidden('#skF_3'(A_78,B_79,C_80),C_80)
      | k4_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_595,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_592])).

tff(c_600,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k3_xboole_0(A_6,k1_xboole_0) = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_595])).

tff(c_640,plain,(
    ! [A_84,C_85] :
      ( r2_hidden('#skF_3'(A_84,A_84,C_85),C_85)
      | k3_xboole_0(A_84,k1_xboole_0) = C_85 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_595])).

tff(c_170,plain,(
    ! [D_37,B_38,A_39] :
      ( ~ r2_hidden(D_37,B_38)
      | ~ r2_hidden(D_37,k4_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_173,plain,(
    ! [D_37,A_12] :
      ( ~ r2_hidden(D_37,k1_xboole_0)
      | ~ r2_hidden(D_37,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_170])).

tff(c_712,plain,(
    ! [A_88,A_89] :
      ( ~ r2_hidden('#skF_3'(A_88,A_88,k1_xboole_0),A_89)
      | k3_xboole_0(A_88,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_640,c_173])).

tff(c_723,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_600,c_712])).

tff(c_1055,plain,(
    ! [A_109,C_110] :
      ( r2_hidden('#skF_3'(A_109,A_109,C_110),C_110)
      | k1_xboole_0 = C_110 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_600])).

tff(c_1089,plain,(
    ! [A_109,C_110,B_2] :
      ( r2_hidden('#skF_3'(A_109,A_109,C_110),B_2)
      | ~ r1_tarski(C_110,B_2)
      | k1_xboole_0 = C_110 ) ),
    inference(resolution,[status(thm)],[c_1055,c_2])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3641,plain,(
    ! [A_222,A_223,B_224] :
      ( ~ r2_hidden('#skF_3'(A_222,A_222,k4_xboole_0(A_223,B_224)),B_224)
      | k4_xboole_0(A_223,B_224) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1055,c_10])).

tff(c_3699,plain,(
    ! [A_223,B_2] :
      ( ~ r1_tarski(k4_xboole_0(A_223,B_2),B_2)
      | k4_xboole_0(A_223,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1089,c_3641])).

tff(c_17856,plain,(
    ! [A_512] :
      ( k4_xboole_0(A_512,k2_relat_1('#skF_5')) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_512,k2_relat_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_17839,c_3699])).

tff(c_17869,plain,(
    k4_xboole_0('#skF_4',k2_relat_1('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1721,c_17856])).

tff(c_28,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18181,plain,(
    k3_xboole_0('#skF_4',k2_relat_1('#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17869,c_28])).

tff(c_18275,plain,(
    k3_xboole_0('#skF_4',k2_relat_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18181])).

tff(c_299,plain,(
    ! [B_57,A_58] :
      ( k3_xboole_0(k2_relat_1(B_57),A_58) = k2_relat_1(k8_relat_1(A_58,B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_34,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_115,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_34])).

tff(c_312,plain,(
    ! [A_58,B_57] :
      ( k3_xboole_0(A_58,k2_relat_1(B_57)) = k2_relat_1(k8_relat_1(A_58,B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_115])).

tff(c_18443,plain,
    ( k2_relat_1(k8_relat_1('#skF_4','#skF_5')) = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18275,c_312])).

tff(c_18510,plain,(
    k2_relat_1(k8_relat_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18443])).

tff(c_18512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_18510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:57:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.35/3.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.35/3.62  
% 9.35/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.35/3.62  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.35/3.62  
% 9.35/3.62  %Foreground sorts:
% 9.35/3.62  
% 9.35/3.62  
% 9.35/3.62  %Background operators:
% 9.35/3.62  
% 9.35/3.62  
% 9.35/3.62  %Foreground operators:
% 9.35/3.62  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.35/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.35/3.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.35/3.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.35/3.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.35/3.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.35/3.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.35/3.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.35/3.62  tff('#skF_5', type, '#skF_5': $i).
% 9.35/3.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.35/3.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.35/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.35/3.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.35/3.62  tff('#skF_4', type, '#skF_4': $i).
% 9.35/3.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.35/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.35/3.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.35/3.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.35/3.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.35/3.62  
% 9.35/3.63  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 9.35/3.63  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.35/3.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.35/3.63  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.35/3.63  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.35/3.63  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 9.35/3.63  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.35/3.63  tff(f_52, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.35/3.63  tff(c_38, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.35/3.63  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.35/3.63  tff(c_26, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.35/3.63  tff(c_175, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.63  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.35/3.63  tff(c_1647, plain, (![A_147, B_148, B_149]: (r2_hidden('#skF_1'(k4_xboole_0(A_147, B_148), B_149), A_147) | r1_tarski(k4_xboole_0(A_147, B_148), B_149))), inference(resolution, [status(thm)], [c_175, c_12])).
% 9.35/3.63  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.63  tff(c_1721, plain, (![A_147, B_148]: (r1_tarski(k4_xboole_0(A_147, B_148), A_147))), inference(resolution, [status(thm)], [c_1647, c_4])).
% 9.35/3.63  tff(c_40, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.35/3.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.63  tff(c_247, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.63  tff(c_1377, plain, (![A_121, B_122, B_123]: (r2_hidden('#skF_1'(A_121, B_122), B_123) | ~r1_tarski(A_121, B_123) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_6, c_247])).
% 9.35/3.63  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.63  tff(c_17751, plain, (![A_505, B_506, B_507, B_508]: (r2_hidden('#skF_1'(A_505, B_506), B_507) | ~r1_tarski(B_508, B_507) | ~r1_tarski(A_505, B_508) | r1_tarski(A_505, B_506))), inference(resolution, [status(thm)], [c_1377, c_2])).
% 9.35/3.63  tff(c_17818, plain, (![A_509, B_510]: (r2_hidden('#skF_1'(A_509, B_510), k2_relat_1('#skF_5')) | ~r1_tarski(A_509, '#skF_4') | r1_tarski(A_509, B_510))), inference(resolution, [status(thm)], [c_40, c_17751])).
% 9.35/3.63  tff(c_17839, plain, (![A_511]: (~r1_tarski(A_511, '#skF_4') | r1_tarski(A_511, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_17818, c_4])).
% 9.35/3.63  tff(c_197, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.35/3.63  tff(c_218, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_197])).
% 9.35/3.63  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.35/3.63  tff(c_592, plain, (![A_78, B_79, C_80]: (~r2_hidden('#skF_2'(A_78, B_79, C_80), B_79) | r2_hidden('#skF_3'(A_78, B_79, C_80), C_80) | k4_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.35/3.63  tff(c_595, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_592])).
% 9.35/3.63  tff(c_600, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k3_xboole_0(A_6, k1_xboole_0)=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_595])).
% 9.35/3.63  tff(c_640, plain, (![A_84, C_85]: (r2_hidden('#skF_3'(A_84, A_84, C_85), C_85) | k3_xboole_0(A_84, k1_xboole_0)=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_595])).
% 9.35/3.63  tff(c_170, plain, (![D_37, B_38, A_39]: (~r2_hidden(D_37, B_38) | ~r2_hidden(D_37, k4_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.35/3.63  tff(c_173, plain, (![D_37, A_12]: (~r2_hidden(D_37, k1_xboole_0) | ~r2_hidden(D_37, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_170])).
% 9.35/3.63  tff(c_712, plain, (![A_88, A_89]: (~r2_hidden('#skF_3'(A_88, A_88, k1_xboole_0), A_89) | k3_xboole_0(A_88, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_640, c_173])).
% 9.35/3.63  tff(c_723, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_600, c_712])).
% 9.35/3.63  tff(c_1055, plain, (![A_109, C_110]: (r2_hidden('#skF_3'(A_109, A_109, C_110), C_110) | k1_xboole_0=C_110)), inference(demodulation, [status(thm), theory('equality')], [c_723, c_600])).
% 9.35/3.63  tff(c_1089, plain, (![A_109, C_110, B_2]: (r2_hidden('#skF_3'(A_109, A_109, C_110), B_2) | ~r1_tarski(C_110, B_2) | k1_xboole_0=C_110)), inference(resolution, [status(thm)], [c_1055, c_2])).
% 9.35/3.63  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.35/3.63  tff(c_3641, plain, (![A_222, A_223, B_224]: (~r2_hidden('#skF_3'(A_222, A_222, k4_xboole_0(A_223, B_224)), B_224) | k4_xboole_0(A_223, B_224)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1055, c_10])).
% 9.35/3.63  tff(c_3699, plain, (![A_223, B_2]: (~r1_tarski(k4_xboole_0(A_223, B_2), B_2) | k4_xboole_0(A_223, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1089, c_3641])).
% 9.35/3.63  tff(c_17856, plain, (![A_512]: (k4_xboole_0(A_512, k2_relat_1('#skF_5'))=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_512, k2_relat_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_17839, c_3699])).
% 9.35/3.63  tff(c_17869, plain, (k4_xboole_0('#skF_4', k2_relat_1('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1721, c_17856])).
% 9.35/3.63  tff(c_28, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.35/3.63  tff(c_18181, plain, (k3_xboole_0('#skF_4', k2_relat_1('#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17869, c_28])).
% 9.35/3.63  tff(c_18275, plain, (k3_xboole_0('#skF_4', k2_relat_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18181])).
% 9.35/3.63  tff(c_299, plain, (![B_57, A_58]: (k3_xboole_0(k2_relat_1(B_57), A_58)=k2_relat_1(k8_relat_1(A_58, B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.35/3.63  tff(c_30, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.35/3.63  tff(c_85, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.35/3.63  tff(c_109, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_30, c_85])).
% 9.35/3.63  tff(c_34, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.35/3.63  tff(c_115, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_109, c_34])).
% 9.35/3.63  tff(c_312, plain, (![A_58, B_57]: (k3_xboole_0(A_58, k2_relat_1(B_57))=k2_relat_1(k8_relat_1(A_58, B_57)) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_299, c_115])).
% 9.35/3.63  tff(c_18443, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))='#skF_4' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18275, c_312])).
% 9.35/3.63  tff(c_18510, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18443])).
% 9.35/3.63  tff(c_18512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_18510])).
% 9.35/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.35/3.63  
% 9.35/3.63  Inference rules
% 9.35/3.63  ----------------------
% 9.35/3.63  #Ref     : 0
% 9.35/3.63  #Sup     : 4555
% 9.35/3.63  #Fact    : 0
% 9.35/3.63  #Define  : 0
% 9.35/3.63  #Split   : 0
% 9.35/3.63  #Chain   : 0
% 9.35/3.63  #Close   : 0
% 9.35/3.63  
% 9.35/3.63  Ordering : KBO
% 9.35/3.63  
% 9.35/3.63  Simplification rules
% 9.35/3.63  ----------------------
% 9.35/3.63  #Subsume      : 826
% 9.35/3.63  #Demod        : 5251
% 9.35/3.63  #Tautology    : 1714
% 9.35/3.63  #SimpNegUnit  : 1
% 9.35/3.64  #BackRed      : 8
% 9.35/3.64  
% 9.35/3.64  #Partial instantiations: 0
% 9.35/3.64  #Strategies tried      : 1
% 9.35/3.64  
% 9.35/3.64  Timing (in seconds)
% 9.35/3.64  ----------------------
% 9.35/3.64  Preprocessing        : 0.30
% 9.35/3.64  Parsing              : 0.16
% 9.35/3.64  CNF conversion       : 0.02
% 9.35/3.64  Main loop            : 2.58
% 9.35/3.64  Inferencing          : 0.58
% 9.35/3.64  Reduction            : 1.16
% 9.35/3.64  Demodulation         : 1.00
% 9.35/3.64  BG Simplification    : 0.07
% 9.35/3.64  Subsumption          : 0.61
% 9.35/3.64  Abstraction          : 0.11
% 9.35/3.64  MUC search           : 0.00
% 9.35/3.64  Cooper               : 0.00
% 9.35/3.64  Total                : 2.91
% 9.35/3.64  Index Insertion      : 0.00
% 9.35/3.64  Index Deletion       : 0.00
% 9.35/3.64  Index Matching       : 0.00
% 9.35/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
