%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:08 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 198 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_464,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(B_59,k10_relat_1(B_59,A_60)) = A_60
      | ~ r1_tarski(A_60,k2_relat_1(B_59))
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_472,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_464])).

tff(c_480,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_472])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_724,plain,(
    ! [C_72,A_73,B_74] :
      ( k3_xboole_0(k10_relat_1(C_72,A_73),k10_relat_1(C_72,B_74)) = k10_relat_1(C_72,k3_xboole_0(A_73,B_74))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_764,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_724])).

tff(c_781,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_764])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(A_41,B_42)) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_486,plain,(
    ! [A_61,B_62,B_63] : r1_tarski(A_61,k2_xboole_0(k2_xboole_0(A_61,B_62),B_63)) ),
    inference(resolution,[status(thm)],[c_168,c_8])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_526,plain,(
    ! [A_61,B_62,B_63] : k3_xboole_0(A_61,k2_xboole_0(k2_xboole_0(A_61,B_62),B_63)) = A_61 ),
    inference(resolution,[status(thm)],[c_486,c_14])).

tff(c_133,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_43,B_44] : k2_xboole_0(k3_xboole_0(A_43,B_44),A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_1378,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(k3_xboole_0(A_95,B_96),C_97)
      | ~ r1_tarski(A_95,C_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_8])).

tff(c_9372,plain,(
    ! [A_222,B_223,C_224] :
      ( k3_xboole_0(k3_xboole_0(A_222,B_223),C_224) = k3_xboole_0(A_222,B_223)
      | ~ r1_tarski(A_222,C_224) ) ),
    inference(resolution,[status(thm)],[c_1378,c_14])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_263,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(B_48,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_118])).

tff(c_20,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_269,plain,(
    ! [B_48,A_47] : k3_xboole_0(B_48,A_47) = k3_xboole_0(A_47,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_20])).

tff(c_148,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_147,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_530,plain,(
    ! [A_64,B_65,B_66] : r1_tarski(k3_xboole_0(A_64,B_65),k2_xboole_0(A_64,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_486])).

tff(c_600,plain,(
    ! [B_67] : r1_tarski(k3_xboole_0('#skF_1',B_67),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_530])).

tff(c_614,plain,(
    ! [B_48] : r1_tarski(k3_xboole_0(B_48,'#skF_1'),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_600])).

tff(c_15911,plain,(
    ! [A_312,B_313] :
      ( r1_tarski(k3_xboole_0(A_312,B_313),k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_312,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9372,c_614])).

tff(c_16039,plain,(
    ! [A_314] :
      ( r1_tarski(A_314,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_314,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_15911])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k9_relat_1(B_22,k10_relat_1(B_22,A_21)) = A_21
      | ~ r1_tarski(A_21,k2_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16081,plain,(
    ! [A_314] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_314)) = A_314
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_314,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16039,c_24])).

tff(c_24614,plain,(
    ! [A_378] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_378)) = A_378
      | ~ r1_tarski(A_378,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_16081])).

tff(c_24650,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_24614])).

tff(c_24674,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_480,c_24650])).

tff(c_286,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,A_50) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_20])).

tff(c_307,plain,(
    ! [B_49,A_50] : r1_tarski(k3_xboole_0(B_49,A_50),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_12])).

tff(c_24907,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24674,c_307])).

tff(c_24977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/4.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/4.39  
% 10.01/4.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/4.39  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.01/4.39  
% 10.01/4.39  %Foreground sorts:
% 10.01/4.39  
% 10.01/4.39  
% 10.01/4.39  %Background operators:
% 10.01/4.39  
% 10.01/4.39  
% 10.01/4.39  %Foreground operators:
% 10.01/4.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.01/4.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/4.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.01/4.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.01/4.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.01/4.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.01/4.39  tff('#skF_2', type, '#skF_2': $i).
% 10.01/4.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.01/4.39  tff('#skF_3', type, '#skF_3': $i).
% 10.01/4.39  tff('#skF_1', type, '#skF_1': $i).
% 10.01/4.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/4.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.01/4.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.01/4.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/4.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.01/4.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.01/4.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.01/4.39  
% 10.13/4.41  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 10.13/4.41  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.13/4.41  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 10.13/4.41  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.13/4.41  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 10.13/4.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.13/4.41  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.13/4.41  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.13/4.41  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.13/4.41  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.13/4.41  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.13/4.41  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.13/4.41  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.13/4.41  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.13/4.41  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.13/4.41  tff(c_464, plain, (![B_59, A_60]: (k9_relat_1(B_59, k10_relat_1(B_59, A_60))=A_60 | ~r1_tarski(A_60, k2_relat_1(B_59)) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.13/4.41  tff(c_472, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_464])).
% 10.13/4.41  tff(c_480, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_472])).
% 10.13/4.41  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.13/4.41  tff(c_71, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.13/4.41  tff(c_84, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_71])).
% 10.13/4.41  tff(c_724, plain, (![C_72, A_73, B_74]: (k3_xboole_0(k10_relat_1(C_72, A_73), k10_relat_1(C_72, B_74))=k10_relat_1(C_72, k3_xboole_0(A_73, B_74)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.13/4.41  tff(c_764, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_724])).
% 10.13/4.41  tff(c_781, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_764])).
% 10.13/4.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.13/4.41  tff(c_159, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(k2_xboole_0(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.13/4.41  tff(c_168, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_6, c_159])).
% 10.13/4.41  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.13/4.41  tff(c_486, plain, (![A_61, B_62, B_63]: (r1_tarski(A_61, k2_xboole_0(k2_xboole_0(A_61, B_62), B_63)))), inference(resolution, [status(thm)], [c_168, c_8])).
% 10.13/4.41  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.13/4.41  tff(c_526, plain, (![A_61, B_62, B_63]: (k3_xboole_0(A_61, k2_xboole_0(k2_xboole_0(A_61, B_62), B_63))=A_61)), inference(resolution, [status(thm)], [c_486, c_14])).
% 10.13/4.41  tff(c_133, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.13/4.41  tff(c_197, plain, (![A_43, B_44]: (k2_xboole_0(k3_xboole_0(A_43, B_44), A_43)=A_43)), inference(resolution, [status(thm)], [c_12, c_133])).
% 10.13/4.41  tff(c_1378, plain, (![A_95, B_96, C_97]: (r1_tarski(k3_xboole_0(A_95, B_96), C_97) | ~r1_tarski(A_95, C_97))), inference(superposition, [status(thm), theory('equality')], [c_197, c_8])).
% 10.13/4.41  tff(c_9372, plain, (![A_222, B_223, C_224]: (k3_xboole_0(k3_xboole_0(A_222, B_223), C_224)=k3_xboole_0(A_222, B_223) | ~r1_tarski(A_222, C_224))), inference(resolution, [status(thm)], [c_1378, c_14])).
% 10.13/4.41  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.13/4.41  tff(c_118, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.13/4.41  tff(c_263, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(B_48, A_47))), inference(superposition, [status(thm), theory('equality')], [c_16, c_118])).
% 10.13/4.41  tff(c_20, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.13/4.41  tff(c_269, plain, (![B_48, A_47]: (k3_xboole_0(B_48, A_47)=k3_xboole_0(A_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_263, c_20])).
% 10.13/4.41  tff(c_148, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_133])).
% 10.13/4.41  tff(c_147, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_133])).
% 10.13/4.41  tff(c_530, plain, (![A_64, B_65, B_66]: (r1_tarski(k3_xboole_0(A_64, B_65), k2_xboole_0(A_64, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_486])).
% 10.13/4.41  tff(c_600, plain, (![B_67]: (r1_tarski(k3_xboole_0('#skF_1', B_67), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_530])).
% 10.13/4.41  tff(c_614, plain, (![B_48]: (r1_tarski(k3_xboole_0(B_48, '#skF_1'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_269, c_600])).
% 10.13/4.41  tff(c_15911, plain, (![A_312, B_313]: (r1_tarski(k3_xboole_0(A_312, B_313), k2_relat_1('#skF_3')) | ~r1_tarski(A_312, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9372, c_614])).
% 10.13/4.41  tff(c_16039, plain, (![A_314]: (r1_tarski(A_314, k2_relat_1('#skF_3')) | ~r1_tarski(A_314, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_15911])).
% 10.13/4.41  tff(c_24, plain, (![B_22, A_21]: (k9_relat_1(B_22, k10_relat_1(B_22, A_21))=A_21 | ~r1_tarski(A_21, k2_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.13/4.41  tff(c_16081, plain, (![A_314]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_314))=A_314 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_314, '#skF_1'))), inference(resolution, [status(thm)], [c_16039, c_24])).
% 10.13/4.41  tff(c_24614, plain, (![A_378]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_378))=A_378 | ~r1_tarski(A_378, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_16081])).
% 10.13/4.41  tff(c_24650, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_781, c_24614])).
% 10.13/4.41  tff(c_24674, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_480, c_24650])).
% 10.13/4.41  tff(c_286, plain, (![B_49, A_50]: (k3_xboole_0(B_49, A_50)=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_263, c_20])).
% 10.13/4.41  tff(c_307, plain, (![B_49, A_50]: (r1_tarski(k3_xboole_0(B_49, A_50), A_50))), inference(superposition, [status(thm), theory('equality')], [c_286, c_12])).
% 10.13/4.41  tff(c_24907, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24674, c_307])).
% 10.13/4.41  tff(c_24977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24907])).
% 10.13/4.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.13/4.41  
% 10.13/4.41  Inference rules
% 10.13/4.41  ----------------------
% 10.13/4.41  #Ref     : 0
% 10.13/4.41  #Sup     : 6210
% 10.13/4.41  #Fact    : 0
% 10.13/4.41  #Define  : 0
% 10.13/4.41  #Split   : 3
% 10.13/4.41  #Chain   : 0
% 10.13/4.41  #Close   : 0
% 10.13/4.41  
% 10.13/4.41  Ordering : KBO
% 10.13/4.41  
% 10.13/4.41  Simplification rules
% 10.13/4.41  ----------------------
% 10.13/4.41  #Subsume      : 549
% 10.13/4.41  #Demod        : 5228
% 10.13/4.41  #Tautology    : 3453
% 10.13/4.41  #SimpNegUnit  : 1
% 10.13/4.41  #BackRed      : 4
% 10.13/4.41  
% 10.13/4.41  #Partial instantiations: 0
% 10.13/4.41  #Strategies tried      : 1
% 10.13/4.41  
% 10.13/4.41  Timing (in seconds)
% 10.13/4.41  ----------------------
% 10.13/4.41  Preprocessing        : 0.29
% 10.13/4.41  Parsing              : 0.15
% 10.13/4.41  CNF conversion       : 0.02
% 10.13/4.41  Main loop            : 3.23
% 10.13/4.41  Inferencing          : 0.61
% 10.13/4.41  Reduction            : 1.78
% 10.13/4.41  Demodulation         : 1.57
% 10.13/4.41  BG Simplification    : 0.08
% 10.13/4.41  Subsumption          : 0.60
% 10.13/4.41  Abstraction          : 0.12
% 10.13/4.41  MUC search           : 0.00
% 10.13/4.41  Cooper               : 0.00
% 10.13/4.41  Total                : 3.55
% 10.13/4.41  Index Insertion      : 0.00
% 10.13/4.41  Index Deletion       : 0.00
% 10.13/4.41  Index Matching       : 0.00
% 10.13/4.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
