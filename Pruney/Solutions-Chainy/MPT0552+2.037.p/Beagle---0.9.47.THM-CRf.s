%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:01 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 135 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(k7_relat_1(A_29,B_30))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k2_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)),k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_57,B_58,C_59] : r1_tarski(k3_xboole_0(A_57,k2_xboole_0(B_58,C_59)),k2_xboole_0(B_58,C_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_104,plain,(
    ! [A_57,A_14,B_15] : r1_tarski(k3_xboole_0(A_57,A_14),k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_108,plain,(
    ! [A_57,A_14] : r1_tarski(k3_xboole_0(A_57,A_14),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_28,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(k7_relat_1(B_35,A_34)) = k9_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_759,plain,(
    ! [C_171,B_172,A_173] :
      ( k7_relat_1(k7_relat_1(C_171,B_172),A_173) = k7_relat_1(C_171,A_173)
      | ~ r1_tarski(A_173,B_172)
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_37,A_36)),k2_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_818,plain,(
    ! [C_183,A_184,B_185] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_183,A_184)),k2_relat_1(k7_relat_1(C_183,B_185)))
      | ~ v1_relat_1(k7_relat_1(C_183,B_185))
      | ~ r1_tarski(A_184,B_185)
      | ~ v1_relat_1(C_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_30])).

tff(c_841,plain,(
    ! [B_189,A_190,A_191] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_189,A_190)),k9_relat_1(B_189,A_191))
      | ~ v1_relat_1(k7_relat_1(B_189,A_191))
      | ~ r1_tarski(A_190,A_191)
      | ~ v1_relat_1(B_189)
      | ~ v1_relat_1(B_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_818])).

tff(c_861,plain,(
    ! [B_195,A_196,A_197] :
      ( r1_tarski(k9_relat_1(B_195,A_196),k9_relat_1(B_195,A_197))
      | ~ v1_relat_1(k7_relat_1(B_195,A_197))
      | ~ r1_tarski(A_196,A_197)
      | ~ v1_relat_1(B_195)
      | ~ v1_relat_1(B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_841])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [C_76,B_77,A_78] :
      ( k7_relat_1(k7_relat_1(C_76,B_77),A_78) = k7_relat_1(C_76,A_78)
      | ~ r1_tarski(A_78,B_77)
      | ~ v1_relat_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_183,plain,(
    ! [C_82,A_83,B_84] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_82,A_83)),k2_relat_1(k7_relat_1(C_82,B_84)))
      | ~ v1_relat_1(k7_relat_1(C_82,B_84))
      | ~ r1_tarski(A_83,B_84)
      | ~ v1_relat_1(C_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_30])).

tff(c_248,plain,(
    ! [B_99,A_100,A_101] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_99,A_100)),k9_relat_1(B_99,A_101))
      | ~ v1_relat_1(k7_relat_1(B_99,A_101))
      | ~ r1_tarski(A_100,A_101)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_183])).

tff(c_731,plain,(
    ! [B_168,A_169,A_170] :
      ( r1_tarski(k9_relat_1(B_168,A_169),k9_relat_1(B_168,A_170))
      | ~ v1_relat_1(k7_relat_1(B_168,A_170))
      | ~ r1_tarski(A_169,A_170)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_248])).

tff(c_133,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(A_70,k3_xboole_0(B_71,C_72))
      | ~ r1_tarski(A_70,C_72)
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_133,c_32])).

tff(c_147,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_738,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_731,c_147])).

tff(c_749,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4,c_738])).

tff(c_752,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_749])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_752])).

tff(c_757,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_864,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_861,c_757])).

tff(c_873,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_108,c_864])).

tff(c_882,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_873])).

tff(c_886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:38:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.49  
% 3.25/1.49  %Foreground sorts:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Background operators:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Foreground operators:
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.25/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.25/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.25/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.25/1.49  
% 3.25/1.50  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 3.25/1.50  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.25/1.50  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.25/1.50  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.25/1.50  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.25/1.50  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.25/1.50  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 3.25/1.50  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 3.25/1.50  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.25/1.50  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.25/1.50  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.25/1.50  tff(c_24, plain, (![A_29, B_30]: (v1_relat_1(k7_relat_1(A_29, B_30)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.25/1.50  tff(c_12, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.50  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.50  tff(c_10, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13)), k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.50  tff(c_101, plain, (![A_57, B_58, C_59]: (r1_tarski(k3_xboole_0(A_57, k2_xboole_0(B_58, C_59)), k2_xboole_0(B_58, C_59)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.25/1.50  tff(c_104, plain, (![A_57, A_14, B_15]: (r1_tarski(k3_xboole_0(A_57, A_14), k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_101])).
% 3.25/1.50  tff(c_108, plain, (![A_57, A_14]: (r1_tarski(k3_xboole_0(A_57, A_14), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104])).
% 3.25/1.50  tff(c_28, plain, (![B_35, A_34]: (k2_relat_1(k7_relat_1(B_35, A_34))=k9_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.50  tff(c_759, plain, (![C_171, B_172, A_173]: (k7_relat_1(k7_relat_1(C_171, B_172), A_173)=k7_relat_1(C_171, A_173) | ~r1_tarski(A_173, B_172) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.25/1.50  tff(c_30, plain, (![B_37, A_36]: (r1_tarski(k2_relat_1(k7_relat_1(B_37, A_36)), k2_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.50  tff(c_818, plain, (![C_183, A_184, B_185]: (r1_tarski(k2_relat_1(k7_relat_1(C_183, A_184)), k2_relat_1(k7_relat_1(C_183, B_185))) | ~v1_relat_1(k7_relat_1(C_183, B_185)) | ~r1_tarski(A_184, B_185) | ~v1_relat_1(C_183))), inference(superposition, [status(thm), theory('equality')], [c_759, c_30])).
% 3.25/1.50  tff(c_841, plain, (![B_189, A_190, A_191]: (r1_tarski(k2_relat_1(k7_relat_1(B_189, A_190)), k9_relat_1(B_189, A_191)) | ~v1_relat_1(k7_relat_1(B_189, A_191)) | ~r1_tarski(A_190, A_191) | ~v1_relat_1(B_189) | ~v1_relat_1(B_189))), inference(superposition, [status(thm), theory('equality')], [c_28, c_818])).
% 3.25/1.50  tff(c_861, plain, (![B_195, A_196, A_197]: (r1_tarski(k9_relat_1(B_195, A_196), k9_relat_1(B_195, A_197)) | ~v1_relat_1(k7_relat_1(B_195, A_197)) | ~r1_tarski(A_196, A_197) | ~v1_relat_1(B_195) | ~v1_relat_1(B_195) | ~v1_relat_1(B_195))), inference(superposition, [status(thm), theory('equality')], [c_28, c_841])).
% 3.25/1.50  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.50  tff(c_148, plain, (![C_76, B_77, A_78]: (k7_relat_1(k7_relat_1(C_76, B_77), A_78)=k7_relat_1(C_76, A_78) | ~r1_tarski(A_78, B_77) | ~v1_relat_1(C_76))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.25/1.50  tff(c_183, plain, (![C_82, A_83, B_84]: (r1_tarski(k2_relat_1(k7_relat_1(C_82, A_83)), k2_relat_1(k7_relat_1(C_82, B_84))) | ~v1_relat_1(k7_relat_1(C_82, B_84)) | ~r1_tarski(A_83, B_84) | ~v1_relat_1(C_82))), inference(superposition, [status(thm), theory('equality')], [c_148, c_30])).
% 3.25/1.50  tff(c_248, plain, (![B_99, A_100, A_101]: (r1_tarski(k2_relat_1(k7_relat_1(B_99, A_100)), k9_relat_1(B_99, A_101)) | ~v1_relat_1(k7_relat_1(B_99, A_101)) | ~r1_tarski(A_100, A_101) | ~v1_relat_1(B_99) | ~v1_relat_1(B_99))), inference(superposition, [status(thm), theory('equality')], [c_28, c_183])).
% 3.25/1.50  tff(c_731, plain, (![B_168, A_169, A_170]: (r1_tarski(k9_relat_1(B_168, A_169), k9_relat_1(B_168, A_170)) | ~v1_relat_1(k7_relat_1(B_168, A_170)) | ~r1_tarski(A_169, A_170) | ~v1_relat_1(B_168) | ~v1_relat_1(B_168) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_28, c_248])).
% 3.25/1.50  tff(c_133, plain, (![A_70, B_71, C_72]: (r1_tarski(A_70, k3_xboole_0(B_71, C_72)) | ~r1_tarski(A_70, C_72) | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.50  tff(c_32, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.25/1.50  tff(c_137, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_133, c_32])).
% 3.25/1.50  tff(c_147, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_137])).
% 3.25/1.50  tff(c_738, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_731, c_147])).
% 3.25/1.50  tff(c_749, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4, c_738])).
% 3.25/1.50  tff(c_752, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_749])).
% 3.25/1.50  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_752])).
% 3.25/1.50  tff(c_757, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_137])).
% 3.25/1.50  tff(c_864, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_861, c_757])).
% 3.25/1.50  tff(c_873, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_108, c_864])).
% 3.25/1.50  tff(c_882, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_873])).
% 3.25/1.50  tff(c_886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_882])).
% 3.25/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  Inference rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Ref     : 0
% 3.25/1.50  #Sup     : 237
% 3.25/1.50  #Fact    : 0
% 3.25/1.50  #Define  : 0
% 3.25/1.50  #Split   : 1
% 3.25/1.50  #Chain   : 0
% 3.25/1.50  #Close   : 0
% 3.25/1.50  
% 3.25/1.50  Ordering : KBO
% 3.25/1.50  
% 3.25/1.50  Simplification rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Subsume      : 42
% 3.25/1.50  #Demod        : 11
% 3.25/1.50  #Tautology    : 32
% 3.25/1.50  #SimpNegUnit  : 0
% 3.25/1.50  #BackRed      : 0
% 3.25/1.50  
% 3.25/1.50  #Partial instantiations: 0
% 3.25/1.50  #Strategies tried      : 1
% 3.25/1.50  
% 3.25/1.50  Timing (in seconds)
% 3.25/1.50  ----------------------
% 3.25/1.50  Preprocessing        : 0.31
% 3.25/1.50  Parsing              : 0.17
% 3.25/1.50  CNF conversion       : 0.02
% 3.25/1.50  Main loop            : 0.43
% 3.25/1.50  Inferencing          : 0.17
% 3.25/1.50  Reduction            : 0.11
% 3.25/1.50  Demodulation         : 0.08
% 3.25/1.50  BG Simplification    : 0.03
% 3.25/1.50  Subsumption          : 0.10
% 3.25/1.50  Abstraction          : 0.03
% 3.25/1.50  MUC search           : 0.00
% 3.25/1.50  Cooper               : 0.00
% 3.25/1.50  Total                : 0.77
% 3.25/1.50  Index Insertion      : 0.00
% 3.25/1.50  Index Deletion       : 0.00
% 3.25/1.50  Index Matching       : 0.00
% 3.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
