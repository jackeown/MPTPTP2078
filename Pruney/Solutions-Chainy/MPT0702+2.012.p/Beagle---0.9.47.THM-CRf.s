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

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 191 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 437 expanded)
%              Number of equality atoms :   21 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_936,plain,(
    ! [C_82,A_83,B_84] :
      ( k3_xboole_0(k9_relat_1(C_82,A_83),k9_relat_1(C_82,B_84)) = k9_relat_1(C_82,k3_xboole_0(A_83,B_84))
      | ~ v2_funct_1(C_82)
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_98,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_960,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_114])).

tff(c_1001,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_960])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k10_relat_1(B_22,k9_relat_1(B_22,A_21)),A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1185,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_24])).

tff(c_1195,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_1185])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_148,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_40,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [B_26,A_27] : r1_tarski(k3_xboole_0(B_26,A_27),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_165,plain,(
    ! [B_26,A_27] : k2_xboole_0(k3_xboole_0(B_26,A_27),A_27) = A_27 ),
    inference(resolution,[status(thm)],[c_55,c_148])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_266,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(k2_xboole_0(A_44,B_46),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [A_47,B_48] : r1_tarski(A_47,k2_xboole_0(A_47,B_48)) ),
    inference(resolution,[status(thm)],[c_8,c_266])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_414,plain,(
    ! [A_53,B_54,B_55] : r1_tarski(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) ),
    inference(resolution,[status(thm)],[c_287,c_10])).

tff(c_458,plain,(
    ! [B_56,A_57,B_58] : r1_tarski(k3_xboole_0(B_56,A_57),k2_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_414])).

tff(c_507,plain,(
    ! [B_59] : r1_tarski(k3_xboole_0(B_59,'#skF_1'),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_458])).

tff(c_523,plain,(
    ! [A_1] : r1_tarski(k3_xboole_0('#skF_1',A_1),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_507])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k10_relat_1(B_20,k9_relat_1(B_20,A_19)))
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1182,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_22])).

tff(c_1193,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_523,c_1182])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9746,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1193,c_4])).

tff(c_9755,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_9746])).

tff(c_790,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,k10_relat_1(B_76,k9_relat_1(B_76,A_75)))
      | ~ r1_tarski(A_75,k1_relat_1(B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_809,plain,(
    ! [B_76,A_75] :
      ( k10_relat_1(B_76,k9_relat_1(B_76,A_75)) = A_75
      | ~ r1_tarski(k10_relat_1(B_76,k9_relat_1(B_76,A_75)),A_75)
      | ~ r1_tarski(A_75,k1_relat_1(B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_790,c_4])).

tff(c_9768,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9755,c_809])).

tff(c_9792,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_14,c_9755,c_9768])).

tff(c_9935,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9792,c_55])).

tff(c_9975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_9935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.58  
% 7.01/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.58  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.01/2.58  
% 7.01/2.58  %Foreground sorts:
% 7.01/2.58  
% 7.01/2.58  
% 7.01/2.58  %Background operators:
% 7.01/2.58  
% 7.01/2.58  
% 7.01/2.58  %Foreground operators:
% 7.01/2.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.01/2.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.01/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.01/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.01/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.01/2.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.01/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.01/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.01/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.01/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.01/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.01/2.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.01/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.01/2.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.01/2.58  
% 7.20/2.60  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 7.20/2.60  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.20/2.60  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 7.20/2.60  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.20/2.60  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 7.20/2.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.20/2.60  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.20/2.60  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.20/2.60  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.20/2.60  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 7.20/2.60  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.20/2.60  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_936, plain, (![C_82, A_83, B_84]: (k3_xboole_0(k9_relat_1(C_82, A_83), k9_relat_1(C_82, B_84))=k9_relat_1(C_82, k3_xboole_0(A_83, B_84)) | ~v2_funct_1(C_82) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.20/2.60  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.20/2.60  tff(c_98, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.20/2.60  tff(c_114, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_98])).
% 7.20/2.60  tff(c_960, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_936, c_114])).
% 7.20/2.60  tff(c_1001, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_960])).
% 7.20/2.60  tff(c_24, plain, (![B_22, A_21]: (r1_tarski(k10_relat_1(B_22, k9_relat_1(B_22, A_21)), A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.20/2.60  tff(c_1185, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1001, c_24])).
% 7.20/2.60  tff(c_1195, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_1185])).
% 7.20/2.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.20/2.60  tff(c_148, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.20/2.60  tff(c_167, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_148])).
% 7.20/2.60  tff(c_40, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.20/2.60  tff(c_55, plain, (![B_26, A_27]: (r1_tarski(k3_xboole_0(B_26, A_27), A_27))), inference(superposition, [status(thm), theory('equality')], [c_40, c_14])).
% 7.20/2.60  tff(c_165, plain, (![B_26, A_27]: (k2_xboole_0(k3_xboole_0(B_26, A_27), A_27)=A_27)), inference(resolution, [status(thm)], [c_55, c_148])).
% 7.20/2.60  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.20/2.60  tff(c_266, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(k2_xboole_0(A_44, B_46), C_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.20/2.60  tff(c_287, plain, (![A_47, B_48]: (r1_tarski(A_47, k2_xboole_0(A_47, B_48)))), inference(resolution, [status(thm)], [c_8, c_266])).
% 7.20/2.60  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.20/2.60  tff(c_414, plain, (![A_53, B_54, B_55]: (r1_tarski(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55)))), inference(resolution, [status(thm)], [c_287, c_10])).
% 7.20/2.60  tff(c_458, plain, (![B_56, A_57, B_58]: (r1_tarski(k3_xboole_0(B_56, A_57), k2_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_414])).
% 7.20/2.60  tff(c_507, plain, (![B_59]: (r1_tarski(k3_xboole_0(B_59, '#skF_1'), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_458])).
% 7.20/2.60  tff(c_523, plain, (![A_1]: (r1_tarski(k3_xboole_0('#skF_1', A_1), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_507])).
% 7.20/2.60  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(A_19, k10_relat_1(B_20, k9_relat_1(B_20, A_19))) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.20/2.60  tff(c_1182, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1001, c_22])).
% 7.20/2.60  tff(c_1193, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_523, c_1182])).
% 7.20/2.60  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.20/2.60  tff(c_9746, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1193, c_4])).
% 7.20/2.60  tff(c_9755, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_9746])).
% 7.20/2.60  tff(c_790, plain, (![A_75, B_76]: (r1_tarski(A_75, k10_relat_1(B_76, k9_relat_1(B_76, A_75))) | ~r1_tarski(A_75, k1_relat_1(B_76)) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.20/2.60  tff(c_809, plain, (![B_76, A_75]: (k10_relat_1(B_76, k9_relat_1(B_76, A_75))=A_75 | ~r1_tarski(k10_relat_1(B_76, k9_relat_1(B_76, A_75)), A_75) | ~r1_tarski(A_75, k1_relat_1(B_76)) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_790, c_4])).
% 7.20/2.60  tff(c_9768, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9755, c_809])).
% 7.20/2.60  tff(c_9792, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_14, c_9755, c_9768])).
% 7.20/2.60  tff(c_9935, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9792, c_55])).
% 7.20/2.60  tff(c_9975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_9935])).
% 7.20/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.60  
% 7.20/2.60  Inference rules
% 7.20/2.60  ----------------------
% 7.20/2.60  #Ref     : 0
% 7.20/2.60  #Sup     : 2467
% 7.20/2.60  #Fact    : 0
% 7.20/2.60  #Define  : 0
% 7.20/2.60  #Split   : 2
% 7.20/2.60  #Chain   : 0
% 7.20/2.60  #Close   : 0
% 7.20/2.60  
% 7.20/2.60  Ordering : KBO
% 7.20/2.60  
% 7.20/2.60  Simplification rules
% 7.20/2.60  ----------------------
% 7.20/2.60  #Subsume      : 171
% 7.20/2.60  #Demod        : 2083
% 7.20/2.60  #Tautology    : 1532
% 7.20/2.60  #SimpNegUnit  : 1
% 7.20/2.60  #BackRed      : 3
% 7.20/2.60  
% 7.20/2.60  #Partial instantiations: 0
% 7.20/2.60  #Strategies tried      : 1
% 7.20/2.60  
% 7.20/2.60  Timing (in seconds)
% 7.20/2.60  ----------------------
% 7.20/2.60  Preprocessing        : 0.28
% 7.20/2.60  Parsing              : 0.16
% 7.20/2.60  CNF conversion       : 0.02
% 7.20/2.60  Main loop            : 1.55
% 7.20/2.60  Inferencing          : 0.40
% 7.20/2.60  Reduction            : 0.74
% 7.20/2.60  Demodulation         : 0.62
% 7.20/2.60  BG Simplification    : 0.04
% 7.20/2.60  Subsumption          : 0.26
% 7.20/2.60  Abstraction          : 0.07
% 7.20/2.60  MUC search           : 0.00
% 7.20/2.60  Cooper               : 0.00
% 7.20/2.60  Total                : 1.86
% 7.20/2.60  Index Insertion      : 0.00
% 7.20/2.60  Index Deletion       : 0.00
% 7.20/2.60  Index Matching       : 0.00
% 7.20/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
