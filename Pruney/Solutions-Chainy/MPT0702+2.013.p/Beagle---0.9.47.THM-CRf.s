%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:04 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 131 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 275 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(A_29,B_30)
      | ~ r1_tarski(A_29,k3_xboole_0(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [B_32,C_33] : r1_tarski(k3_xboole_0(B_32,C_33),B_32) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_556,plain,(
    ! [B_59,C_60] : k3_xboole_0(k3_xboole_0(B_59,C_60),B_59) = k3_xboole_0(B_59,C_60) ),
    inference(resolution,[status(thm)],[c_135,c_12])).

tff(c_159,plain,(
    ! [B_32,C_33] : k3_xboole_0(k3_xboole_0(B_32,C_33),B_32) = k3_xboole_0(B_32,C_33) ),
    inference(resolution,[status(thm)],[c_135,c_12])).

tff(c_559,plain,(
    ! [B_59,C_60] : k3_xboole_0(k3_xboole_0(B_59,C_60),k3_xboole_0(B_59,C_60)) = k3_xboole_0(k3_xboole_0(B_59,C_60),B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_159])).

tff(c_640,plain,(
    ! [B_59,C_60] : k3_xboole_0(B_59,k3_xboole_0(B_59,C_60)) = k3_xboole_0(B_59,C_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2,c_559])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1010,plain,(
    ! [C_66,A_67,B_68] :
      ( k3_xboole_0(k9_relat_1(C_66,A_67),k9_relat_1(C_66,B_68)) = k9_relat_1(C_66,k3_xboole_0(A_67,B_68))
      | ~ v2_funct_1(C_66)
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_1044,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_78])).

tff(c_1086,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1044])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k10_relat_1(B_18,k9_relat_1(B_18,A_17)),A_17)
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1104,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_20])).

tff(c_1114,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1104])).

tff(c_79,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k3_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [B_36,C_37,C_38] : r1_tarski(k3_xboole_0(k3_xboole_0(B_36,C_37),C_38),B_36) ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_298,plain,(
    ! [A_42,B_43,C_44] : r1_tarski(k3_xboole_0(k3_xboole_0(A_42,B_43),C_44),B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_320,plain,(
    ! [C_44] : r1_tarski(k3_xboole_0('#skF_1',C_44),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_298])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,k10_relat_1(B_16,k9_relat_1(B_16,A_15)))
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1101,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_18])).

tff(c_1112,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_320,c_1101])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5823,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1112,c_4])).

tff(c_5829,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_5823])).

tff(c_456,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,k10_relat_1(B_53,k9_relat_1(B_53,A_52)))
      | ~ r1_tarski(A_52,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_463,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,k10_relat_1(B_53,k9_relat_1(B_53,A_52))) = A_52
      | ~ r1_tarski(A_52,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_456,c_12])).

tff(c_5848,plain,
    ( k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5829,c_463])).

tff(c_5862,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_640,c_5848])).

tff(c_153,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_5963,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5862,c_153])).

tff(c_5999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_5963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.34/2.07  
% 5.34/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.08  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.36/2.08  
% 5.36/2.08  %Foreground sorts:
% 5.36/2.08  
% 5.36/2.08  
% 5.36/2.08  %Background operators:
% 5.36/2.08  
% 5.36/2.08  
% 5.36/2.08  %Foreground operators:
% 5.36/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.36/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.36/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.36/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.36/2.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.36/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.36/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.36/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.36/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.36/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.36/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.36/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.36/2.08  
% 5.36/2.09  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.36/2.09  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.36/2.09  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.36/2.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.36/2.09  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 5.36/2.09  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 5.36/2.09  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.36/2.09  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.36/2.09  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.09  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.09  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.09  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.36/2.09  tff(c_68, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/2.09  tff(c_80, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_68])).
% 5.36/2.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.36/2.09  tff(c_117, plain, (![A_29, B_30, C_31]: (r1_tarski(A_29, B_30) | ~r1_tarski(A_29, k3_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.36/2.09  tff(c_135, plain, (![B_32, C_33]: (r1_tarski(k3_xboole_0(B_32, C_33), B_32))), inference(resolution, [status(thm)], [c_8, c_117])).
% 5.36/2.09  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/2.09  tff(c_556, plain, (![B_59, C_60]: (k3_xboole_0(k3_xboole_0(B_59, C_60), B_59)=k3_xboole_0(B_59, C_60))), inference(resolution, [status(thm)], [c_135, c_12])).
% 5.36/2.09  tff(c_159, plain, (![B_32, C_33]: (k3_xboole_0(k3_xboole_0(B_32, C_33), B_32)=k3_xboole_0(B_32, C_33))), inference(resolution, [status(thm)], [c_135, c_12])).
% 5.36/2.09  tff(c_559, plain, (![B_59, C_60]: (k3_xboole_0(k3_xboole_0(B_59, C_60), k3_xboole_0(B_59, C_60))=k3_xboole_0(k3_xboole_0(B_59, C_60), B_59))), inference(superposition, [status(thm), theory('equality')], [c_556, c_159])).
% 5.36/2.09  tff(c_640, plain, (![B_59, C_60]: (k3_xboole_0(B_59, k3_xboole_0(B_59, C_60))=k3_xboole_0(B_59, C_60))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2, c_559])).
% 5.36/2.09  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.09  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.09  tff(c_1010, plain, (![C_66, A_67, B_68]: (k3_xboole_0(k9_relat_1(C_66, A_67), k9_relat_1(C_66, B_68))=k9_relat_1(C_66, k3_xboole_0(A_67, B_68)) | ~v2_funct_1(C_66) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.36/2.09  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.09  tff(c_78, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_68])).
% 5.36/2.09  tff(c_1044, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1010, c_78])).
% 5.36/2.09  tff(c_1086, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1044])).
% 5.36/2.09  tff(c_20, plain, (![B_18, A_17]: (r1_tarski(k10_relat_1(B_18, k9_relat_1(B_18, A_17)), A_17) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.36/2.09  tff(c_1104, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_20])).
% 5.36/2.09  tff(c_1114, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1104])).
% 5.36/2.09  tff(c_79, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_68])).
% 5.36/2.09  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.36/2.09  tff(c_207, plain, (![B_36, C_37, C_38]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_36, C_37), C_38), B_36))), inference(resolution, [status(thm)], [c_135, c_10])).
% 5.36/2.09  tff(c_298, plain, (![A_42, B_43, C_44]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_42, B_43), C_44), B_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_207])).
% 5.36/2.09  tff(c_320, plain, (![C_44]: (r1_tarski(k3_xboole_0('#skF_1', C_44), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_298])).
% 5.36/2.09  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k10_relat_1(B_16, k9_relat_1(B_16, A_15))) | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.36/2.09  tff(c_1101, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_18])).
% 5.36/2.09  tff(c_1112, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_320, c_1101])).
% 5.36/2.09  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.36/2.09  tff(c_5823, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1112, c_4])).
% 5.36/2.09  tff(c_5829, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_5823])).
% 5.36/2.09  tff(c_456, plain, (![A_52, B_53]: (r1_tarski(A_52, k10_relat_1(B_53, k9_relat_1(B_53, A_52))) | ~r1_tarski(A_52, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.36/2.09  tff(c_463, plain, (![A_52, B_53]: (k3_xboole_0(A_52, k10_relat_1(B_53, k9_relat_1(B_53, A_52)))=A_52 | ~r1_tarski(A_52, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_456, c_12])).
% 5.36/2.09  tff(c_5848, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5829, c_463])).
% 5.36/2.09  tff(c_5862, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_640, c_5848])).
% 5.36/2.09  tff(c_153, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 5.36/2.09  tff(c_5963, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5862, c_153])).
% 5.36/2.09  tff(c_5999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_5963])).
% 5.36/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.09  
% 5.36/2.09  Inference rules
% 5.36/2.09  ----------------------
% 5.36/2.09  #Ref     : 0
% 5.36/2.09  #Sup     : 1437
% 5.36/2.09  #Fact    : 0
% 5.36/2.09  #Define  : 0
% 5.36/2.09  #Split   : 2
% 5.36/2.09  #Chain   : 0
% 5.36/2.09  #Close   : 0
% 5.36/2.09  
% 5.36/2.09  Ordering : KBO
% 5.36/2.09  
% 5.36/2.09  Simplification rules
% 5.36/2.09  ----------------------
% 5.36/2.09  #Subsume      : 159
% 5.36/2.09  #Demod        : 1217
% 5.36/2.09  #Tautology    : 840
% 5.36/2.09  #SimpNegUnit  : 1
% 5.36/2.09  #BackRed      : 5
% 5.36/2.09  
% 5.36/2.09  #Partial instantiations: 0
% 5.36/2.09  #Strategies tried      : 1
% 5.36/2.09  
% 5.36/2.09  Timing (in seconds)
% 5.36/2.09  ----------------------
% 5.36/2.09  Preprocessing        : 0.30
% 5.36/2.09  Parsing              : 0.17
% 5.36/2.09  CNF conversion       : 0.02
% 5.36/2.09  Main loop            : 1.02
% 5.36/2.09  Inferencing          : 0.31
% 5.36/2.09  Reduction            : 0.45
% 5.36/2.09  Demodulation         : 0.37
% 5.36/2.09  BG Simplification    : 0.03
% 5.36/2.09  Subsumption          : 0.17
% 5.36/2.09  Abstraction          : 0.04
% 5.36/2.10  MUC search           : 0.00
% 5.36/2.10  Cooper               : 0.00
% 5.36/2.10  Total                : 1.35
% 5.36/2.10  Index Insertion      : 0.00
% 5.36/2.10  Index Deletion       : 0.00
% 5.36/2.10  Index Matching       : 0.00
% 5.36/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
