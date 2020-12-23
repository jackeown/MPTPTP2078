%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 182 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_254,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(B_46,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_18,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_18])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_298,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_12])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k10_relat_1(B_20,k9_relat_1(B_20,A_19)))
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_797,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k10_relat_1(B_74,k9_relat_1(B_74,A_75)),A_75)
      | ~ v2_funct_1(B_74)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5374,plain,(
    ! [B_164,A_165] :
      ( k10_relat_1(B_164,k9_relat_1(B_164,A_165)) = A_165
      | ~ r1_tarski(A_165,k10_relat_1(B_164,k9_relat_1(B_164,A_165)))
      | ~ v2_funct_1(B_164)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(resolution,[status(thm)],[c_797,c_2])).

tff(c_6343,plain,(
    ! [B_180,A_181] :
      ( k10_relat_1(B_180,k9_relat_1(B_180,A_181)) = A_181
      | ~ v2_funct_1(B_180)
      | ~ v1_funct_1(B_180)
      | ~ r1_tarski(A_181,k1_relat_1(B_180))
      | ~ v1_relat_1(B_180) ) ),
    inference(resolution,[status(thm)],[c_22,c_5374])).

tff(c_6384,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_6343])).

tff(c_6417,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_6384])).

tff(c_979,plain,(
    ! [C_85,A_86,B_87] :
      ( k3_xboole_0(k9_relat_1(C_85,A_86),k9_relat_1(C_85,B_87)) = k9_relat_1(C_85,k3_xboole_0(A_86,B_87))
      | ~ v2_funct_1(C_85)
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_88,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_1015,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_101])).

tff(c_1044,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_1015])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1800,plain,(
    ! [B_105,A_106] :
      ( k2_xboole_0(k10_relat_1(B_105,k9_relat_1(B_105,A_106)),A_106) = A_106
      | ~ v2_funct_1(B_105)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_797,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6605,plain,(
    ! [B_183,A_184,C_185] :
      ( r1_tarski(k10_relat_1(B_183,k9_relat_1(B_183,A_184)),C_185)
      | ~ r1_tarski(A_184,C_185)
      | ~ v2_funct_1(B_183)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1800,c_8])).

tff(c_6634,plain,(
    ! [C_185] :
      ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),C_185)
      | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),C_185)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_6605])).

tff(c_6648,plain,(
    ! [C_186] :
      ( r1_tarski('#skF_1',C_186)
      | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),C_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_6417,c_6634])).

tff(c_6696,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_6648])).

tff(c_6727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_6696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/2.11  
% 5.40/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/2.11  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.40/2.11  
% 5.40/2.11  %Foreground sorts:
% 5.40/2.11  
% 5.40/2.11  
% 5.40/2.11  %Background operators:
% 5.40/2.11  
% 5.40/2.11  
% 5.40/2.11  %Foreground operators:
% 5.40/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.40/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.40/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.40/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.40/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.40/2.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.40/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.40/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.40/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/2.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.40/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.40/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.40/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.40/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.40/2.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.40/2.11  
% 5.47/2.12  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.47/2.12  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.47/2.12  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.47/2.12  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.47/2.12  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.47/2.12  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.47/2.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.47/2.12  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 5.47/2.12  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.47/2.12  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.47/2.12  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.47/2.12  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/2.12  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.47/2.12  tff(c_73, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.47/2.12  tff(c_254, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(B_46, A_45))), inference(superposition, [status(thm), theory('equality')], [c_16, c_73])).
% 5.47/2.12  tff(c_18, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.47/2.12  tff(c_277, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_254, c_18])).
% 5.47/2.12  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.47/2.12  tff(c_298, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_277, c_12])).
% 5.47/2.12  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/2.12  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/2.12  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/2.12  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/2.12  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(A_19, k10_relat_1(B_20, k9_relat_1(B_20, A_19))) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.47/2.12  tff(c_797, plain, (![B_74, A_75]: (r1_tarski(k10_relat_1(B_74, k9_relat_1(B_74, A_75)), A_75) | ~v2_funct_1(B_74) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.47/2.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.47/2.12  tff(c_5374, plain, (![B_164, A_165]: (k10_relat_1(B_164, k9_relat_1(B_164, A_165))=A_165 | ~r1_tarski(A_165, k10_relat_1(B_164, k9_relat_1(B_164, A_165))) | ~v2_funct_1(B_164) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(resolution, [status(thm)], [c_797, c_2])).
% 5.47/2.12  tff(c_6343, plain, (![B_180, A_181]: (k10_relat_1(B_180, k9_relat_1(B_180, A_181))=A_181 | ~v2_funct_1(B_180) | ~v1_funct_1(B_180) | ~r1_tarski(A_181, k1_relat_1(B_180)) | ~v1_relat_1(B_180))), inference(resolution, [status(thm)], [c_22, c_5374])).
% 5.47/2.12  tff(c_6384, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_6343])).
% 5.47/2.12  tff(c_6417, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_6384])).
% 5.47/2.12  tff(c_979, plain, (![C_85, A_86, B_87]: (k3_xboole_0(k9_relat_1(C_85, A_86), k9_relat_1(C_85, B_87))=k9_relat_1(C_85, k3_xboole_0(A_86, B_87)) | ~v2_funct_1(C_85) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.47/2.12  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/2.12  tff(c_88, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.47/2.12  tff(c_101, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_88])).
% 5.47/2.12  tff(c_1015, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_979, c_101])).
% 5.47/2.12  tff(c_1044, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_1015])).
% 5.47/2.12  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.47/2.12  tff(c_1800, plain, (![B_105, A_106]: (k2_xboole_0(k10_relat_1(B_105, k9_relat_1(B_105, A_106)), A_106)=A_106 | ~v2_funct_1(B_105) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_797, c_10])).
% 5.47/2.12  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/2.12  tff(c_6605, plain, (![B_183, A_184, C_185]: (r1_tarski(k10_relat_1(B_183, k9_relat_1(B_183, A_184)), C_185) | ~r1_tarski(A_184, C_185) | ~v2_funct_1(B_183) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(superposition, [status(thm), theory('equality')], [c_1800, c_8])).
% 5.47/2.12  tff(c_6634, plain, (![C_185]: (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), C_185) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), C_185) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_6605])).
% 5.47/2.12  tff(c_6648, plain, (![C_186]: (r1_tarski('#skF_1', C_186) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), C_186))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_6417, c_6634])).
% 5.47/2.12  tff(c_6696, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_298, c_6648])).
% 5.47/2.12  tff(c_6727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_6696])).
% 5.47/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/2.12  
% 5.47/2.12  Inference rules
% 5.47/2.12  ----------------------
% 5.47/2.12  #Ref     : 0
% 5.47/2.12  #Sup     : 1638
% 5.47/2.12  #Fact    : 0
% 5.47/2.12  #Define  : 0
% 5.47/2.12  #Split   : 2
% 5.47/2.12  #Chain   : 0
% 5.47/2.12  #Close   : 0
% 5.47/2.12  
% 5.47/2.12  Ordering : KBO
% 5.47/2.12  
% 5.47/2.12  Simplification rules
% 5.47/2.12  ----------------------
% 5.47/2.12  #Subsume      : 78
% 5.47/2.12  #Demod        : 1380
% 5.47/2.12  #Tautology    : 1087
% 5.47/2.12  #SimpNegUnit  : 1
% 5.47/2.12  #BackRed      : 0
% 5.47/2.12  
% 5.47/2.12  #Partial instantiations: 0
% 5.47/2.12  #Strategies tried      : 1
% 5.47/2.12  
% 5.47/2.12  Timing (in seconds)
% 5.47/2.12  ----------------------
% 5.47/2.12  Preprocessing        : 0.30
% 5.47/2.12  Parsing              : 0.16
% 5.47/2.12  CNF conversion       : 0.02
% 5.47/2.12  Main loop            : 1.06
% 5.47/2.12  Inferencing          : 0.31
% 5.47/2.12  Reduction            : 0.48
% 5.47/2.12  Demodulation         : 0.40
% 5.47/2.12  BG Simplification    : 0.03
% 5.47/2.13  Subsumption          : 0.17
% 5.47/2.13  Abstraction          : 0.05
% 5.47/2.13  MUC search           : 0.00
% 5.47/2.13  Cooper               : 0.00
% 5.47/2.13  Total                : 1.39
% 5.47/2.13  Index Insertion      : 0.00
% 5.47/2.13  Index Deletion       : 0.00
% 5.47/2.13  Index Matching       : 0.00
% 5.47/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
