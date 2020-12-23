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
% DateTime   : Thu Dec  3 10:04:51 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 131 expanded)
%              Number of equality atoms :   32 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_118,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k3_xboole_0(k2_relat_1(B_17),A_16)) = k10_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [B_23,A_22] : k5_relat_1(k6_relat_1(B_23),k6_relat_1(A_22)) = k6_relat_1(k3_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_279,plain,(
    ! [B_54,A_55] :
      ( k9_relat_1(B_54,k2_relat_1(A_55)) = k2_relat_1(k5_relat_1(A_55,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_303,plain,(
    ! [A_18,B_54] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_18),B_54)) = k9_relat_1(B_54,A_18)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_279])).

tff(c_365,plain,(
    ! [A_64,B_65] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_64),B_65)) = k9_relat_1(B_65,A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_303])).

tff(c_389,plain,(
    ! [A_22,B_23] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_22,B_23))) = k9_relat_1(k6_relat_1(A_22),B_23)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_365])).

tff(c_395,plain,(
    ! [A_22,B_23] : k9_relat_1(k6_relat_1(A_22),B_23) = k3_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_389])).

tff(c_188,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k9_relat_1(B_39,A_40),k2_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [A_18,A_40] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_18),A_40),A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_196,plain,(
    ! [A_18,A_40] : r1_tarski(k9_relat_1(k6_relat_1(A_18),A_40),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_194])).

tff(c_336,plain,(
    ! [B_62,A_63] :
      ( k9_relat_1(B_62,k10_relat_1(B_62,A_63)) = A_63
      | ~ r1_tarski(A_63,k2_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_359,plain,(
    ! [B_62,A_40] :
      ( k9_relat_1(B_62,k10_relat_1(B_62,k9_relat_1(k6_relat_1(k2_relat_1(B_62)),A_40))) = k9_relat_1(k6_relat_1(k2_relat_1(B_62)),A_40)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_196,c_336])).

tff(c_3042,plain,(
    ! [B_127,A_128] :
      ( k9_relat_1(B_127,k10_relat_1(B_127,k3_xboole_0(k2_relat_1(B_127),A_128))) = k3_xboole_0(k2_relat_1(B_127),A_128)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_395,c_359])).

tff(c_3316,plain,(
    ! [B_131,A_132] :
      ( k9_relat_1(B_131,k10_relat_1(B_131,A_132)) = k3_xboole_0(k2_relat_1(B_131),A_132)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3042])).

tff(c_169,plain,(
    ! [A_38] :
      ( k9_relat_1(A_38,k1_relat_1(A_38)) = k2_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_175,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_30])).

tff(c_184,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_175])).

tff(c_3355,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3316,c_184])).

tff(c_3408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_32,c_118,c_3355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.74  
% 4.07/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.74  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.07/1.74  
% 4.07/1.74  %Foreground sorts:
% 4.07/1.74  
% 4.07/1.74  
% 4.07/1.74  %Background operators:
% 4.07/1.74  
% 4.07/1.74  
% 4.07/1.74  %Foreground operators:
% 4.07/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.07/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.07/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.07/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/1.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.07/1.74  
% 4.07/1.75  tff(f_77, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 4.07/1.75  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.07/1.75  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.07/1.75  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 4.07/1.75  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.07/1.75  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.07/1.75  tff(f_70, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.07/1.75  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 4.07/1.75  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.07/1.75  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 4.07/1.75  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 4.07/1.75  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.75  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.75  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.75  tff(c_88, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.07/1.75  tff(c_112, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88])).
% 4.07/1.75  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.07/1.75  tff(c_118, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 4.07/1.75  tff(c_16, plain, (![B_17, A_16]: (k10_relat_1(B_17, k3_xboole_0(k2_relat_1(B_17), A_16))=k10_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.07/1.75  tff(c_22, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.07/1.75  tff(c_20, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.07/1.75  tff(c_28, plain, (![B_23, A_22]: (k5_relat_1(k6_relat_1(B_23), k6_relat_1(A_22))=k6_relat_1(k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.07/1.75  tff(c_279, plain, (![B_54, A_55]: (k9_relat_1(B_54, k2_relat_1(A_55))=k2_relat_1(k5_relat_1(A_55, B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.07/1.75  tff(c_303, plain, (![A_18, B_54]: (k2_relat_1(k5_relat_1(k6_relat_1(A_18), B_54))=k9_relat_1(B_54, A_18) | ~v1_relat_1(B_54) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_279])).
% 4.07/1.75  tff(c_365, plain, (![A_64, B_65]: (k2_relat_1(k5_relat_1(k6_relat_1(A_64), B_65))=k9_relat_1(B_65, A_64) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_303])).
% 4.07/1.75  tff(c_389, plain, (![A_22, B_23]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_22, B_23)))=k9_relat_1(k6_relat_1(A_22), B_23) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_365])).
% 4.07/1.75  tff(c_395, plain, (![A_22, B_23]: (k9_relat_1(k6_relat_1(A_22), B_23)=k3_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_389])).
% 4.07/1.75  tff(c_188, plain, (![B_39, A_40]: (r1_tarski(k9_relat_1(B_39, A_40), k2_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.75  tff(c_194, plain, (![A_18, A_40]: (r1_tarski(k9_relat_1(k6_relat_1(A_18), A_40), A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 4.07/1.75  tff(c_196, plain, (![A_18, A_40]: (r1_tarski(k9_relat_1(k6_relat_1(A_18), A_40), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_194])).
% 4.07/1.75  tff(c_336, plain, (![B_62, A_63]: (k9_relat_1(B_62, k10_relat_1(B_62, A_63))=A_63 | ~r1_tarski(A_63, k2_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.07/1.75  tff(c_359, plain, (![B_62, A_40]: (k9_relat_1(B_62, k10_relat_1(B_62, k9_relat_1(k6_relat_1(k2_relat_1(B_62)), A_40)))=k9_relat_1(k6_relat_1(k2_relat_1(B_62)), A_40) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_196, c_336])).
% 4.07/1.75  tff(c_3042, plain, (![B_127, A_128]: (k9_relat_1(B_127, k10_relat_1(B_127, k3_xboole_0(k2_relat_1(B_127), A_128)))=k3_xboole_0(k2_relat_1(B_127), A_128) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_395, c_359])).
% 4.07/1.75  tff(c_3316, plain, (![B_131, A_132]: (k9_relat_1(B_131, k10_relat_1(B_131, A_132))=k3_xboole_0(k2_relat_1(B_131), A_132) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131) | ~v1_relat_1(B_131))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3042])).
% 4.07/1.75  tff(c_169, plain, (![A_38]: (k9_relat_1(A_38, k1_relat_1(A_38))=k2_relat_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.07/1.75  tff(c_30, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.75  tff(c_175, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_169, c_30])).
% 4.07/1.75  tff(c_184, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_175])).
% 4.07/1.75  tff(c_3355, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3316, c_184])).
% 4.07/1.75  tff(c_3408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_32, c_118, c_3355])).
% 4.07/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.75  
% 4.07/1.75  Inference rules
% 4.07/1.75  ----------------------
% 4.07/1.75  #Ref     : 0
% 4.07/1.75  #Sup     : 802
% 4.07/1.75  #Fact    : 0
% 4.07/1.75  #Define  : 0
% 4.07/1.75  #Split   : 0
% 4.07/1.75  #Chain   : 0
% 4.07/1.75  #Close   : 0
% 4.07/1.75  
% 4.07/1.75  Ordering : KBO
% 4.07/1.75  
% 4.07/1.75  Simplification rules
% 4.07/1.75  ----------------------
% 4.07/1.75  #Subsume      : 68
% 4.07/1.75  #Demod        : 1255
% 4.07/1.75  #Tautology    : 531
% 4.07/1.75  #SimpNegUnit  : 0
% 4.07/1.75  #BackRed      : 2
% 4.07/1.75  
% 4.07/1.75  #Partial instantiations: 0
% 4.07/1.75  #Strategies tried      : 1
% 4.07/1.75  
% 4.07/1.75  Timing (in seconds)
% 4.07/1.75  ----------------------
% 4.07/1.75  Preprocessing        : 0.29
% 4.07/1.75  Parsing              : 0.16
% 4.07/1.75  CNF conversion       : 0.02
% 4.07/1.75  Main loop            : 0.70
% 4.07/1.75  Inferencing          : 0.22
% 4.07/1.75  Reduction            : 0.33
% 4.07/1.75  Demodulation         : 0.28
% 4.07/1.75  BG Simplification    : 0.03
% 4.07/1.76  Subsumption          : 0.09
% 4.07/1.76  Abstraction          : 0.04
% 4.07/1.76  MUC search           : 0.00
% 4.07/1.76  Cooper               : 0.00
% 4.07/1.76  Total                : 1.02
% 4.07/1.76  Index Insertion      : 0.00
% 4.07/1.76  Index Deletion       : 0.00
% 4.07/1.76  Index Matching       : 0.00
% 4.07/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
