%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:57 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 128 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 246 expanded)
%              Number of equality atoms :   24 (  81 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))) = k3_xboole_0(k9_relat_1(C,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k7_relat_1(A_19,B_20))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [A_46,C_47,B_48] :
      ( k3_xboole_0(A_46,k10_relat_1(C_47,B_48)) = k10_relat_1(k7_relat_1(C_47,A_46),B_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [C_47,A_46,B_48] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_47,A_46),B_48),A_46)
      | ~ v1_relat_1(C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_10])).

tff(c_20,plain,(
    ! [A_14,C_18,B_17] :
      ( k9_relat_1(k7_relat_1(A_14,C_18),B_17) = k9_relat_1(A_14,B_17)
      | ~ r1_tarski(B_17,C_18)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_276,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,k9_relat_1(B_68,k1_relat_1(B_68))) = k9_relat_1(B_68,k10_relat_1(B_68,A_67))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_430,plain,(
    ! [A_77,A_78] :
      ( k9_relat_1(A_77,k10_relat_1(A_77,A_78)) = k3_xboole_0(A_78,k2_relat_1(A_77))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_276])).

tff(c_2387,plain,(
    ! [A_196,C_197,A_198] :
      ( k9_relat_1(A_196,k10_relat_1(k7_relat_1(A_196,C_197),A_198)) = k3_xboole_0(A_198,k2_relat_1(k7_relat_1(A_196,C_197)))
      | ~ v1_funct_1(k7_relat_1(A_196,C_197))
      | ~ v1_relat_1(k7_relat_1(A_196,C_197))
      | ~ v1_relat_1(k7_relat_1(A_196,C_197))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_196,C_197),A_198),C_197)
      | ~ v1_relat_1(A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_430])).

tff(c_2401,plain,(
    ! [C_199,A_200,B_201] :
      ( k9_relat_1(C_199,k10_relat_1(k7_relat_1(C_199,A_200),B_201)) = k3_xboole_0(B_201,k2_relat_1(k7_relat_1(C_199,A_200)))
      | ~ v1_funct_1(k7_relat_1(C_199,A_200))
      | ~ v1_relat_1(k7_relat_1(C_199,A_200))
      | ~ v1_relat_1(C_199) ) ),
    inference(resolution,[status(thm)],[c_156,c_2387])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))) != k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_144,plain,
    ( k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_36])).

tff(c_170,plain,(
    k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_144])).

tff(c_2414,plain,
    ( k3_xboole_0('#skF_2',k2_relat_1(k7_relat_1('#skF_3','#skF_1'))) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2401,c_170])).

tff(c_2434,plain,
    ( k3_xboole_0('#skF_2',k2_relat_1(k7_relat_1('#skF_3','#skF_1'))) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2414])).

tff(c_2436,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2434])).

tff(c_2439,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2436])).

tff(c_2443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2439])).

tff(c_2444,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | k3_xboole_0('#skF_2',k2_relat_1(k7_relat_1('#skF_3','#skF_1'))) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2434])).

tff(c_2446,plain,(
    k3_xboole_0('#skF_2',k2_relat_1(k7_relat_1('#skF_3','#skF_1'))) != k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2444])).

tff(c_2449,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2446])).

tff(c_2453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2449])).

tff(c_2454,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2444])).

tff(c_2458,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2454])).

tff(c_2462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.08  
% 5.12/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.08  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.12/2.08  
% 5.12/2.08  %Foreground sorts:
% 5.12/2.08  
% 5.12/2.08  
% 5.12/2.08  %Background operators:
% 5.12/2.08  
% 5.12/2.08  
% 5.12/2.08  %Foreground operators:
% 5.12/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.12/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.12/2.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.12/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.12/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.12/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.12/2.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.12/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.12/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.12/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/2.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.12/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.12/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.12/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.12/2.08  
% 5.12/2.09  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))) = k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_funct_1)).
% 5.12/2.09  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 5.12/2.09  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.12/2.09  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.12/2.09  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.12/2.09  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.12/2.09  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 5.12/2.09  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.12/2.09  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 5.12/2.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.12/2.09  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.12/2.09  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.12/2.09  tff(c_22, plain, (![A_19, B_20]: (v1_funct_1(k7_relat_1(A_19, B_20)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.12/2.09  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/2.09  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.12/2.09  tff(c_135, plain, (![A_46, C_47, B_48]: (k3_xboole_0(A_46, k10_relat_1(C_47, B_48))=k10_relat_1(k7_relat_1(C_47, A_46), B_48) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.12/2.09  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.12/2.09  tff(c_156, plain, (![C_47, A_46, B_48]: (r1_tarski(k10_relat_1(k7_relat_1(C_47, A_46), B_48), A_46) | ~v1_relat_1(C_47))), inference(superposition, [status(thm), theory('equality')], [c_135, c_10])).
% 5.12/2.09  tff(c_20, plain, (![A_14, C_18, B_17]: (k9_relat_1(k7_relat_1(A_14, C_18), B_17)=k9_relat_1(A_14, B_17) | ~r1_tarski(B_17, C_18) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.12/2.09  tff(c_16, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.12/2.09  tff(c_276, plain, (![A_67, B_68]: (k3_xboole_0(A_67, k9_relat_1(B_68, k1_relat_1(B_68)))=k9_relat_1(B_68, k10_relat_1(B_68, A_67)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.12/2.09  tff(c_430, plain, (![A_77, A_78]: (k9_relat_1(A_77, k10_relat_1(A_77, A_78))=k3_xboole_0(A_78, k2_relat_1(A_77)) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_16, c_276])).
% 5.12/2.09  tff(c_2387, plain, (![A_196, C_197, A_198]: (k9_relat_1(A_196, k10_relat_1(k7_relat_1(A_196, C_197), A_198))=k3_xboole_0(A_198, k2_relat_1(k7_relat_1(A_196, C_197))) | ~v1_funct_1(k7_relat_1(A_196, C_197)) | ~v1_relat_1(k7_relat_1(A_196, C_197)) | ~v1_relat_1(k7_relat_1(A_196, C_197)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_196, C_197), A_198), C_197) | ~v1_relat_1(A_196))), inference(superposition, [status(thm), theory('equality')], [c_20, c_430])).
% 5.12/2.09  tff(c_2401, plain, (![C_199, A_200, B_201]: (k9_relat_1(C_199, k10_relat_1(k7_relat_1(C_199, A_200), B_201))=k3_xboole_0(B_201, k2_relat_1(k7_relat_1(C_199, A_200))) | ~v1_funct_1(k7_relat_1(C_199, A_200)) | ~v1_relat_1(k7_relat_1(C_199, A_200)) | ~v1_relat_1(C_199))), inference(resolution, [status(thm)], [c_156, c_2387])).
% 5.12/2.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.09  tff(c_30, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')))!=k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.12/2.09  tff(c_36, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 5.12/2.09  tff(c_144, plain, (k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_135, c_36])).
% 5.12/2.09  tff(c_170, plain, (k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_144])).
% 5.12/2.09  tff(c_2414, plain, (k3_xboole_0('#skF_2', k2_relat_1(k7_relat_1('#skF_3', '#skF_1')))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2401, c_170])).
% 5.12/2.09  tff(c_2434, plain, (k3_xboole_0('#skF_2', k2_relat_1(k7_relat_1('#skF_3', '#skF_1')))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2414])).
% 5.12/2.09  tff(c_2436, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2434])).
% 5.12/2.09  tff(c_2439, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_2436])).
% 5.12/2.09  tff(c_2443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2439])).
% 5.12/2.09  tff(c_2444, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | k3_xboole_0('#skF_2', k2_relat_1(k7_relat_1('#skF_3', '#skF_1')))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_2434])).
% 5.12/2.09  tff(c_2446, plain, (k3_xboole_0('#skF_2', k2_relat_1(k7_relat_1('#skF_3', '#skF_1')))!=k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2444])).
% 5.12/2.09  tff(c_2449, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_2446])).
% 5.12/2.09  tff(c_2453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2449])).
% 5.12/2.09  tff(c_2454, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_2444])).
% 5.12/2.09  tff(c_2458, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2454])).
% 5.12/2.09  tff(c_2462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2458])).
% 5.12/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.09  
% 5.12/2.09  Inference rules
% 5.12/2.09  ----------------------
% 5.12/2.09  #Ref     : 0
% 5.12/2.09  #Sup     : 688
% 5.12/2.09  #Fact    : 0
% 5.12/2.09  #Define  : 0
% 5.12/2.09  #Split   : 2
% 5.12/2.09  #Chain   : 0
% 5.12/2.09  #Close   : 0
% 5.12/2.09  
% 5.12/2.09  Ordering : KBO
% 5.12/2.09  
% 5.12/2.09  Simplification rules
% 5.12/2.09  ----------------------
% 5.12/2.09  #Subsume      : 146
% 5.12/2.09  #Demod        : 21
% 5.12/2.09  #Tautology    : 77
% 5.12/2.09  #SimpNegUnit  : 0
% 5.12/2.09  #BackRed      : 0
% 5.12/2.09  
% 5.12/2.09  #Partial instantiations: 0
% 5.12/2.09  #Strategies tried      : 1
% 5.12/2.09  
% 5.12/2.09  Timing (in seconds)
% 5.12/2.09  ----------------------
% 5.12/2.09  Preprocessing        : 0.44
% 5.12/2.09  Parsing              : 0.26
% 5.12/2.09  CNF conversion       : 0.02
% 5.12/2.09  Main loop            : 0.86
% 5.12/2.09  Inferencing          : 0.31
% 5.12/2.09  Reduction            : 0.24
% 5.12/2.09  Demodulation         : 0.18
% 5.12/2.09  BG Simplification    : 0.05
% 5.12/2.09  Subsumption          : 0.21
% 5.12/2.09  Abstraction          : 0.05
% 5.12/2.09  MUC search           : 0.00
% 5.12/2.09  Cooper               : 0.00
% 5.12/2.09  Total                : 1.33
% 5.12/2.09  Index Insertion      : 0.00
% 5.12/2.09  Index Deletion       : 0.00
% 5.12/2.10  Index Matching       : 0.00
% 5.12/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
