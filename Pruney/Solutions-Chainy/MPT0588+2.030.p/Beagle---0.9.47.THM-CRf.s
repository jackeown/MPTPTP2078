%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   67 (  76 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 (  74 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(k7_relat_1(A_48,B_49))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [C_52,A_50,B_51] :
      ( k7_relat_1(k7_relat_1(C_52,A_50),B_51) = k7_relat_1(C_52,k3_xboole_0(A_50,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [B_54,A_53] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_54,A_53)),k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_202,plain,(
    ! [B_80,A_81] :
      ( k7_relat_1(B_80,A_81) = B_80
      | ~ r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3680,plain,(
    ! [B_199,A_200] :
      ( k7_relat_1(k7_relat_1(B_199,A_200),k1_relat_1(B_199)) = k7_relat_1(B_199,A_200)
      | ~ v1_relat_1(k7_relat_1(B_199,A_200))
      | ~ v1_relat_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_32,c_202])).

tff(c_4705,plain,(
    ! [C_228,A_229] :
      ( k7_relat_1(C_228,k3_xboole_0(A_229,k1_relat_1(C_228))) = k7_relat_1(C_228,A_229)
      | ~ v1_relat_1(k7_relat_1(C_228,A_229))
      | ~ v1_relat_1(C_228)
      | ~ v1_relat_1(C_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3680])).

tff(c_6,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [C_76,D_77,A_78,B_79] : k2_enumset1(C_76,D_77,A_78,B_79) = k2_enumset1(A_78,B_79,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [C_76,D_77,B_79] : k2_enumset1(C_76,D_77,B_79,B_79) = k1_enumset1(B_79,C_76,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_14])).

tff(c_275,plain,(
    ! [B_87,D_88,C_89,A_90] : k2_enumset1(B_87,D_88,C_89,A_90) = k2_enumset1(A_90,B_87,C_89,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_333,plain,(
    ! [D_77,B_79,C_76] : k2_enumset1(D_77,B_79,B_79,C_76) = k1_enumset1(B_79,C_76,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_275])).

tff(c_16,plain,(
    ! [A_22,B_23,C_24,D_25] : k3_enumset1(A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_882,plain,(
    ! [E_127,A_124,B_125,D_126,C_123] : k2_xboole_0(k2_tarski(A_124,B_125),k1_enumset1(C_123,D_126,E_127)) = k3_enumset1(A_124,B_125,C_123,D_126,E_127) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_909,plain,(
    ! [A_16,C_123,D_126,E_127] : k3_enumset1(A_16,A_16,C_123,D_126,E_127) = k2_xboole_0(k1_tarski(A_16),k1_enumset1(C_123,D_126,E_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_882])).

tff(c_2908,plain,(
    ! [A_172,C_173,D_174,E_175] : k2_xboole_0(k1_tarski(A_172),k1_enumset1(C_173,D_174,E_175)) = k2_enumset1(A_172,C_173,D_174,E_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_909])).

tff(c_2932,plain,(
    ! [A_172,A_17,B_18] : k2_xboole_0(k1_tarski(A_172),k2_tarski(A_17,B_18)) = k2_enumset1(A_172,A_17,A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2908])).

tff(c_3332,plain,(
    ! [A_180,A_181,B_182] : k2_xboole_0(k1_tarski(A_180),k2_tarski(A_181,B_182)) = k1_enumset1(A_181,B_182,A_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_2932])).

tff(c_3341,plain,(
    ! [A_180,A_16] : k2_xboole_0(k1_tarski(A_180),k1_tarski(A_16)) = k1_enumset1(A_16,A_16,A_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3332])).

tff(c_3345,plain,(
    ! [A_184,A_183] : k2_tarski(A_184,A_183) = k2_tarski(A_183,A_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_3341])).

tff(c_26,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3402,plain,(
    ! [A_185,A_186] : k1_setfam_1(k2_tarski(A_185,A_186)) = k3_xboole_0(A_186,A_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_3345,c_26])).

tff(c_3408,plain,(
    ! [A_186,A_185] : k3_xboole_0(A_186,A_185) = k3_xboole_0(A_185,A_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_3402,c_26])).

tff(c_36,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3428,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3408,c_36])).

tff(c_4730,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_3428])).

tff(c_4770,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4730])).

tff(c_4774,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_4770])).

tff(c_4778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.90  
% 4.76/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.90  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.76/1.90  
% 4.76/1.90  %Foreground sorts:
% 4.76/1.90  
% 4.76/1.90  
% 4.76/1.90  %Background operators:
% 4.76/1.90  
% 4.76/1.90  
% 4.76/1.90  %Foreground operators:
% 4.76/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.76/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.76/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.76/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.76/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.76/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.76/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.76/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.76/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.76/1.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.76/1.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.76/1.90  
% 5.17/1.92  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 5.17/1.92  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.17/1.92  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 5.17/1.92  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 5.17/1.92  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.17/1.92  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.17/1.92  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.17/1.92  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.17/1.92  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_enumset1)).
% 5.17/1.92  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.17/1.92  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 5.17/1.92  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.17/1.92  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 5.17/1.92  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.17/1.92  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.17/1.92  tff(c_28, plain, (![A_48, B_49]: (v1_relat_1(k7_relat_1(A_48, B_49)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.17/1.92  tff(c_30, plain, (![C_52, A_50, B_51]: (k7_relat_1(k7_relat_1(C_52, A_50), B_51)=k7_relat_1(C_52, k3_xboole_0(A_50, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.17/1.92  tff(c_32, plain, (![B_54, A_53]: (r1_tarski(k1_relat_1(k7_relat_1(B_54, A_53)), k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.17/1.92  tff(c_202, plain, (![B_80, A_81]: (k7_relat_1(B_80, A_81)=B_80 | ~r1_tarski(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.17/1.92  tff(c_3680, plain, (![B_199, A_200]: (k7_relat_1(k7_relat_1(B_199, A_200), k1_relat_1(B_199))=k7_relat_1(B_199, A_200) | ~v1_relat_1(k7_relat_1(B_199, A_200)) | ~v1_relat_1(B_199))), inference(resolution, [status(thm)], [c_32, c_202])).
% 5.17/1.92  tff(c_4705, plain, (![C_228, A_229]: (k7_relat_1(C_228, k3_xboole_0(A_229, k1_relat_1(C_228)))=k7_relat_1(C_228, A_229) | ~v1_relat_1(k7_relat_1(C_228, A_229)) | ~v1_relat_1(C_228) | ~v1_relat_1(C_228))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3680])).
% 5.17/1.92  tff(c_6, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.17/1.92  tff(c_12, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.17/1.92  tff(c_10, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.17/1.92  tff(c_155, plain, (![C_76, D_77, A_78, B_79]: (k2_enumset1(C_76, D_77, A_78, B_79)=k2_enumset1(A_78, B_79, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.17/1.92  tff(c_14, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.17/1.92  tff(c_171, plain, (![C_76, D_77, B_79]: (k2_enumset1(C_76, D_77, B_79, B_79)=k1_enumset1(B_79, C_76, D_77))), inference(superposition, [status(thm), theory('equality')], [c_155, c_14])).
% 5.17/1.92  tff(c_275, plain, (![B_87, D_88, C_89, A_90]: (k2_enumset1(B_87, D_88, C_89, A_90)=k2_enumset1(A_90, B_87, C_89, D_88))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.17/1.92  tff(c_333, plain, (![D_77, B_79, C_76]: (k2_enumset1(D_77, B_79, B_79, C_76)=k1_enumset1(B_79, C_76, D_77))), inference(superposition, [status(thm), theory('equality')], [c_171, c_275])).
% 5.17/1.92  tff(c_16, plain, (![A_22, B_23, C_24, D_25]: (k3_enumset1(A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.17/1.92  tff(c_882, plain, (![E_127, A_124, B_125, D_126, C_123]: (k2_xboole_0(k2_tarski(A_124, B_125), k1_enumset1(C_123, D_126, E_127))=k3_enumset1(A_124, B_125, C_123, D_126, E_127))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.17/1.92  tff(c_909, plain, (![A_16, C_123, D_126, E_127]: (k3_enumset1(A_16, A_16, C_123, D_126, E_127)=k2_xboole_0(k1_tarski(A_16), k1_enumset1(C_123, D_126, E_127)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_882])).
% 5.17/1.92  tff(c_2908, plain, (![A_172, C_173, D_174, E_175]: (k2_xboole_0(k1_tarski(A_172), k1_enumset1(C_173, D_174, E_175))=k2_enumset1(A_172, C_173, D_174, E_175))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_909])).
% 5.17/1.92  tff(c_2932, plain, (![A_172, A_17, B_18]: (k2_xboole_0(k1_tarski(A_172), k2_tarski(A_17, B_18))=k2_enumset1(A_172, A_17, A_17, B_18))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2908])).
% 5.17/1.92  tff(c_3332, plain, (![A_180, A_181, B_182]: (k2_xboole_0(k1_tarski(A_180), k2_tarski(A_181, B_182))=k1_enumset1(A_181, B_182, A_180))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_2932])).
% 5.17/1.92  tff(c_3341, plain, (![A_180, A_16]: (k2_xboole_0(k1_tarski(A_180), k1_tarski(A_16))=k1_enumset1(A_16, A_16, A_180))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3332])).
% 5.17/1.92  tff(c_3345, plain, (![A_184, A_183]: (k2_tarski(A_184, A_183)=k2_tarski(A_183, A_184))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_3341])).
% 5.17/1.92  tff(c_26, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.17/1.92  tff(c_3402, plain, (![A_185, A_186]: (k1_setfam_1(k2_tarski(A_185, A_186))=k3_xboole_0(A_186, A_185))), inference(superposition, [status(thm), theory('equality')], [c_3345, c_26])).
% 5.17/1.92  tff(c_3408, plain, (![A_186, A_185]: (k3_xboole_0(A_186, A_185)=k3_xboole_0(A_185, A_186))), inference(superposition, [status(thm), theory('equality')], [c_3402, c_26])).
% 5.17/1.92  tff(c_36, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.17/1.92  tff(c_3428, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3408, c_36])).
% 5.17/1.92  tff(c_4730, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4705, c_3428])).
% 5.17/1.92  tff(c_4770, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4730])).
% 5.17/1.92  tff(c_4774, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_4770])).
% 5.17/1.92  tff(c_4778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_4774])).
% 5.17/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/1.92  
% 5.17/1.92  Inference rules
% 5.17/1.92  ----------------------
% 5.17/1.92  #Ref     : 0
% 5.17/1.92  #Sup     : 1162
% 5.17/1.92  #Fact    : 0
% 5.17/1.92  #Define  : 0
% 5.17/1.92  #Split   : 0
% 5.17/1.92  #Chain   : 0
% 5.17/1.92  #Close   : 0
% 5.17/1.92  
% 5.17/1.92  Ordering : KBO
% 5.17/1.92  
% 5.17/1.92  Simplification rules
% 5.17/1.92  ----------------------
% 5.17/1.92  #Subsume      : 233
% 5.17/1.92  #Demod        : 725
% 5.17/1.92  #Tautology    : 731
% 5.17/1.92  #SimpNegUnit  : 0
% 5.17/1.92  #BackRed      : 1
% 5.17/1.92  
% 5.17/1.92  #Partial instantiations: 0
% 5.17/1.92  #Strategies tried      : 1
% 5.17/1.92  
% 5.17/1.92  Timing (in seconds)
% 5.17/1.92  ----------------------
% 5.17/1.92  Preprocessing        : 0.31
% 5.17/1.92  Parsing              : 0.17
% 5.17/1.92  CNF conversion       : 0.02
% 5.17/1.92  Main loop            : 0.85
% 5.17/1.92  Inferencing          : 0.28
% 5.17/1.92  Reduction            : 0.40
% 5.17/1.92  Demodulation         : 0.35
% 5.17/1.92  BG Simplification    : 0.03
% 5.17/1.92  Subsumption          : 0.10
% 5.17/1.92  Abstraction          : 0.05
% 5.17/1.92  MUC search           : 0.00
% 5.17/1.92  Cooper               : 0.00
% 5.17/1.92  Total                : 1.19
% 5.17/1.92  Index Insertion      : 0.00
% 5.17/1.92  Index Deletion       : 0.00
% 5.17/1.92  Index Matching       : 0.00
% 5.17/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
