%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   60 (  97 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 226 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1151,plain,(
    ! [C_76,A_77,B_78] :
      ( k3_xboole_0(k9_relat_1(C_76,A_77),k9_relat_1(C_76,B_78)) = k9_relat_1(C_76,k3_xboole_0(A_77,B_78))
      | ~ v2_funct_1(C_76)
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_10])).

tff(c_1195,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_91])).

tff(c_1239,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1195])).

tff(c_466,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k10_relat_1(B_55,k9_relat_1(B_55,A_56)),A_56)
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2218,plain,(
    ! [B_91,B_92,C_93] :
      ( r1_tarski(k10_relat_1(B_91,k9_relat_1(B_91,k3_xboole_0(B_92,C_93))),B_92)
      | ~ v2_funct_1(B_91)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_466,c_8])).

tff(c_2252,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_2218])).

tff(c_2289,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_2252])).

tff(c_724,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,k10_relat_1(B_68,k9_relat_1(B_68,A_67)))
      | ~ r1_tarski(A_67,k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3457,plain,(
    ! [B_112,A_113] :
      ( k10_relat_1(B_112,k9_relat_1(B_112,A_113)) = A_113
      | ~ r1_tarski(k10_relat_1(B_112,k9_relat_1(B_112,A_113)),A_113)
      | ~ r1_tarski(A_113,k1_relat_1(B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_724,c_2])).

tff(c_3460,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2289,c_3457])).

tff(c_3477,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_3460])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k10_relat_1(B_20,k9_relat_1(B_20,A_19)),A_19)
      | ~ v2_funct_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1257,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_22])).

tff(c_1267,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1257])).

tff(c_4136,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3477,c_1267])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_16,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_16])).

tff(c_176,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(A_35,B_36)
      | ~ r1_tarski(A_35,k3_xboole_0(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_179,plain,(
    ! [A_35,A_32,B_31] :
      ( r1_tarski(A_35,A_32)
      | ~ r1_tarski(A_35,k3_xboole_0(B_31,A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_176])).

tff(c_4142,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4136,c_179])).

tff(c_4155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_4142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:56:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.83  
% 4.46/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.83  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.46/1.83  
% 4.46/1.83  %Foreground sorts:
% 4.46/1.83  
% 4.46/1.83  
% 4.46/1.83  %Background operators:
% 4.46/1.83  
% 4.46/1.83  
% 4.46/1.83  %Foreground operators:
% 4.46/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.46/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.46/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.46/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.83  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.46/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.46/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.46/1.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.46/1.84  
% 4.46/1.85  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.46/1.85  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 4.46/1.85  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.46/1.85  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.46/1.85  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.46/1.85  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.46/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.46/1.85  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.46/1.85  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.46/1.85  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.85  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.85  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.85  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.85  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.85  tff(c_1151, plain, (![C_76, A_77, B_78]: (k3_xboole_0(k9_relat_1(C_76, A_77), k9_relat_1(C_76, B_78))=k9_relat_1(C_76, k3_xboole_0(A_77, B_78)) | ~v2_funct_1(C_76) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.46/1.85  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.85  tff(c_10, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.85  tff(c_91, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_10])).
% 4.46/1.85  tff(c_1195, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1151, c_91])).
% 4.46/1.85  tff(c_1239, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1195])).
% 4.46/1.85  tff(c_466, plain, (![B_55, A_56]: (r1_tarski(k10_relat_1(B_55, k9_relat_1(B_55, A_56)), A_56) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.46/1.85  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.85  tff(c_2218, plain, (![B_91, B_92, C_93]: (r1_tarski(k10_relat_1(B_91, k9_relat_1(B_91, k3_xboole_0(B_92, C_93))), B_92) | ~v2_funct_1(B_91) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_466, c_8])).
% 4.46/1.85  tff(c_2252, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_2218])).
% 4.46/1.85  tff(c_2289, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_2252])).
% 4.46/1.85  tff(c_724, plain, (![A_67, B_68]: (r1_tarski(A_67, k10_relat_1(B_68, k9_relat_1(B_68, A_67))) | ~r1_tarski(A_67, k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.46/1.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.85  tff(c_3457, plain, (![B_112, A_113]: (k10_relat_1(B_112, k9_relat_1(B_112, A_113))=A_113 | ~r1_tarski(k10_relat_1(B_112, k9_relat_1(B_112, A_113)), A_113) | ~r1_tarski(A_113, k1_relat_1(B_112)) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_724, c_2])).
% 4.46/1.85  tff(c_3460, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2289, c_3457])).
% 4.46/1.85  tff(c_3477, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_3460])).
% 4.46/1.85  tff(c_22, plain, (![B_20, A_19]: (r1_tarski(k10_relat_1(B_20, k9_relat_1(B_20, A_19)), A_19) | ~v2_funct_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.46/1.85  tff(c_1257, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_22])).
% 4.46/1.85  tff(c_1267, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1257])).
% 4.46/1.85  tff(c_4136, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3477, c_1267])).
% 4.46/1.85  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.85  tff(c_96, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.85  tff(c_120, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 4.46/1.85  tff(c_16, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.85  tff(c_126, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_120, c_16])).
% 4.46/1.85  tff(c_176, plain, (![A_35, B_36, C_37]: (r1_tarski(A_35, B_36) | ~r1_tarski(A_35, k3_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.85  tff(c_179, plain, (![A_35, A_32, B_31]: (r1_tarski(A_35, A_32) | ~r1_tarski(A_35, k3_xboole_0(B_31, A_32)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_176])).
% 4.46/1.85  tff(c_4142, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4136, c_179])).
% 4.46/1.85  tff(c_4155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_4142])).
% 4.46/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.85  
% 4.46/1.85  Inference rules
% 4.46/1.85  ----------------------
% 4.46/1.85  #Ref     : 0
% 4.46/1.85  #Sup     : 994
% 4.46/1.85  #Fact    : 0
% 4.46/1.85  #Define  : 0
% 4.46/1.85  #Split   : 2
% 4.46/1.85  #Chain   : 0
% 4.46/1.85  #Close   : 0
% 4.46/1.85  
% 4.46/1.85  Ordering : KBO
% 4.46/1.85  
% 4.46/1.85  Simplification rules
% 4.46/1.85  ----------------------
% 4.46/1.85  #Subsume      : 109
% 4.46/1.85  #Demod        : 875
% 4.46/1.85  #Tautology    : 620
% 4.46/1.85  #SimpNegUnit  : 1
% 4.46/1.85  #BackRed      : 1
% 4.46/1.85  
% 4.46/1.85  #Partial instantiations: 0
% 4.46/1.85  #Strategies tried      : 1
% 4.46/1.85  
% 4.46/1.85  Timing (in seconds)
% 4.46/1.85  ----------------------
% 4.46/1.85  Preprocessing        : 0.31
% 4.46/1.85  Parsing              : 0.17
% 4.46/1.85  CNF conversion       : 0.02
% 4.46/1.85  Main loop            : 0.75
% 4.46/1.85  Inferencing          : 0.22
% 4.46/1.85  Reduction            : 0.35
% 4.46/1.85  Demodulation         : 0.29
% 4.46/1.85  BG Simplification    : 0.03
% 4.46/1.85  Subsumption          : 0.12
% 4.46/1.85  Abstraction          : 0.04
% 4.46/1.85  MUC search           : 0.00
% 4.46/1.85  Cooper               : 0.00
% 4.46/1.85  Total                : 1.10
% 4.46/1.85  Index Insertion      : 0.00
% 4.46/1.85  Index Deletion       : 0.00
% 4.46/1.85  Index Matching       : 0.00
% 4.46/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
