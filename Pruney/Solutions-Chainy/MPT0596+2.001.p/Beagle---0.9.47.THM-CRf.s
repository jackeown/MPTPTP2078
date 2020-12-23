%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.38s
% Verified   : 
% Statistics : Number of formulae       :   52 (  59 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 (  99 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    k3_xboole_0(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(k3_xboole_0(A_32,C_33),B_34)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [B_35,A_36,B_37] :
      ( r1_tarski(k3_xboole_0(B_35,A_36),B_37)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_155,plain,(
    ! [B_46] :
      ( r1_tarski(k2_relat_1('#skF_2'),B_46)
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_1')),B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_90])).

tff(c_159,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_162,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k8_relat_1(A_11,B_12) = B_12
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,
    ( k8_relat_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_12])).

tff(c_171,plain,(
    k8_relat_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_165])).

tff(c_18,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k5_relat_1(B_10,k6_relat_1(A_9)) = k8_relat_1(A_9,B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_211,plain,(
    ! [A_47,B_48,C_49] :
      ( k5_relat_1(k5_relat_1(A_47,B_48),C_49) = k5_relat_1(A_47,k5_relat_1(B_48,C_49))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_233,plain,(
    ! [B_10,A_9,C_49] :
      ( k5_relat_1(B_10,k5_relat_1(k6_relat_1(A_9),C_49)) = k5_relat_1(k8_relat_1(A_9,B_10),C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_211])).

tff(c_1627,plain,(
    ! [B_98,A_99,C_100] :
      ( k5_relat_1(B_98,k5_relat_1(k6_relat_1(A_99),C_100)) = k5_relat_1(k8_relat_1(A_99,B_98),C_100)
      | ~ v1_relat_1(C_100)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_233])).

tff(c_4135,plain,(
    ! [A_179,B_180,B_181] :
      ( k5_relat_1(k8_relat_1(A_179,B_180),B_181) = k5_relat_1(B_180,k7_relat_1(B_181,A_179))
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1627])).

tff(c_4188,plain,(
    ! [B_181] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_181,'#skF_1')) = k5_relat_1('#skF_2',B_181)
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_4135])).

tff(c_4219,plain,(
    ! [B_182] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_182,'#skF_1')) = k5_relat_1('#skF_2',B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4188])).

tff(c_20,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4237,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4219,c_20])).

tff(c_4257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.11  
% 5.17/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.11  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.17/2.11  
% 5.17/2.11  %Foreground sorts:
% 5.17/2.11  
% 5.17/2.11  
% 5.17/2.11  %Background operators:
% 5.17/2.11  
% 5.17/2.11  
% 5.17/2.11  %Foreground operators:
% 5.17/2.11  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.17/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.17/2.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.17/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.17/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.17/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/2.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.17/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/2.11  
% 5.38/2.12  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_relat_1)).
% 5.38/2.12  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.38/2.12  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.38/2.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.38/2.12  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 5.38/2.12  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 5.38/2.12  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.38/2.12  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.38/2.12  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 5.38/2.12  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.38/2.12  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.38/2.12  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.38/2.12  tff(c_16, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.38/2.12  tff(c_22, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.38/2.12  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.38/2.12  tff(c_65, plain, (k3_xboole_0(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_6])).
% 5.38/2.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.38/2.12  tff(c_72, plain, (![A_32, C_33, B_34]: (r1_tarski(k3_xboole_0(A_32, C_33), B_34) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.38/2.12  tff(c_90, plain, (![B_35, A_36, B_37]: (r1_tarski(k3_xboole_0(B_35, A_36), B_37) | ~r1_tarski(A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 5.38/2.12  tff(c_155, plain, (![B_46]: (r1_tarski(k2_relat_1('#skF_2'), B_46) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_1')), B_46))), inference(superposition, [status(thm), theory('equality')], [c_65, c_90])).
% 5.38/2.12  tff(c_159, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_155])).
% 5.38/2.12  tff(c_162, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_159])).
% 5.38/2.12  tff(c_12, plain, (![A_11, B_12]: (k8_relat_1(A_11, B_12)=B_12 | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.38/2.12  tff(c_165, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_162, c_12])).
% 5.38/2.12  tff(c_171, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_165])).
% 5.38/2.12  tff(c_18, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.38/2.12  tff(c_8, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.38/2.12  tff(c_10, plain, (![B_10, A_9]: (k5_relat_1(B_10, k6_relat_1(A_9))=k8_relat_1(A_9, B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.38/2.12  tff(c_211, plain, (![A_47, B_48, C_49]: (k5_relat_1(k5_relat_1(A_47, B_48), C_49)=k5_relat_1(A_47, k5_relat_1(B_48, C_49)) | ~v1_relat_1(C_49) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.38/2.12  tff(c_233, plain, (![B_10, A_9, C_49]: (k5_relat_1(B_10, k5_relat_1(k6_relat_1(A_9), C_49))=k5_relat_1(k8_relat_1(A_9, B_10), C_49) | ~v1_relat_1(C_49) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(B_10) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_211])).
% 5.38/2.12  tff(c_1627, plain, (![B_98, A_99, C_100]: (k5_relat_1(B_98, k5_relat_1(k6_relat_1(A_99), C_100))=k5_relat_1(k8_relat_1(A_99, B_98), C_100) | ~v1_relat_1(C_100) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_233])).
% 5.38/2.12  tff(c_4135, plain, (![A_179, B_180, B_181]: (k5_relat_1(k8_relat_1(A_179, B_180), B_181)=k5_relat_1(B_180, k7_relat_1(B_181, A_179)) | ~v1_relat_1(B_181) | ~v1_relat_1(B_180) | ~v1_relat_1(B_181))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1627])).
% 5.38/2.12  tff(c_4188, plain, (![B_181]: (k5_relat_1('#skF_2', k7_relat_1(B_181, '#skF_1'))=k5_relat_1('#skF_2', B_181) | ~v1_relat_1(B_181) | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_181))), inference(superposition, [status(thm), theory('equality')], [c_171, c_4135])).
% 5.38/2.12  tff(c_4219, plain, (![B_182]: (k5_relat_1('#skF_2', k7_relat_1(B_182, '#skF_1'))=k5_relat_1('#skF_2', B_182) | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4188])).
% 5.38/2.12  tff(c_20, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.38/2.12  tff(c_4237, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4219, c_20])).
% 5.38/2.12  tff(c_4257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_4237])).
% 5.38/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.12  
% 5.38/2.12  Inference rules
% 5.38/2.12  ----------------------
% 5.38/2.12  #Ref     : 0
% 5.38/2.12  #Sup     : 1121
% 5.38/2.12  #Fact    : 0
% 5.38/2.12  #Define  : 0
% 5.38/2.12  #Split   : 1
% 5.38/2.12  #Chain   : 0
% 5.38/2.12  #Close   : 0
% 5.38/2.12  
% 5.38/2.12  Ordering : KBO
% 5.38/2.12  
% 5.38/2.12  Simplification rules
% 5.38/2.12  ----------------------
% 5.38/2.12  #Subsume      : 280
% 5.38/2.12  #Demod        : 388
% 5.38/2.12  #Tautology    : 243
% 5.38/2.12  #SimpNegUnit  : 0
% 5.38/2.12  #BackRed      : 0
% 5.38/2.12  
% 5.38/2.12  #Partial instantiations: 0
% 5.38/2.12  #Strategies tried      : 1
% 5.38/2.12  
% 5.38/2.12  Timing (in seconds)
% 5.38/2.12  ----------------------
% 5.38/2.12  Preprocessing        : 0.29
% 5.38/2.12  Parsing              : 0.15
% 5.38/2.13  CNF conversion       : 0.02
% 5.38/2.13  Main loop            : 0.95
% 5.38/2.13  Inferencing          : 0.30
% 5.38/2.13  Reduction            : 0.32
% 5.38/2.13  Demodulation         : 0.25
% 5.38/2.13  BG Simplification    : 0.04
% 5.38/2.13  Subsumption          : 0.22
% 5.38/2.13  Abstraction          : 0.05
% 5.38/2.13  MUC search           : 0.00
% 5.38/2.13  Cooper               : 0.00
% 5.38/2.13  Total                : 1.27
% 5.38/2.13  Index Insertion      : 0.00
% 5.38/2.13  Index Deletion       : 0.00
% 5.38/2.13  Index Matching       : 0.00
% 5.38/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
