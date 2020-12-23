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
% DateTime   : Thu Dec  3 10:00:07 EST 2020

% Result     : Theorem 14.64s
% Output     : CNFRefutation 14.64s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 141 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 266 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_46,plain,(
    k2_relat_1(k8_relat_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_775,plain,(
    ! [A_111,B_112,B_113] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_111,B_112),B_113),A_111)
      | r1_tarski(k4_xboole_0(A_111,B_112),B_113) ) ),
    inference(resolution,[status(thm)],[c_195,c_12])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_201,plain,(
    ! [D_48,B_49,A_50] :
      ( ~ r2_hidden(D_48,B_49)
      | ~ r2_hidden(D_48,k4_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [A_50,B_49,B_2] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_50,B_49),B_2),B_49)
      | r1_tarski(k4_xboole_0(A_50,B_49),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_201])).

tff(c_819,plain,(
    ! [A_111,B_113] : r1_tarski(k4_xboole_0(A_111,A_111),B_113) ),
    inference(resolution,[status(thm)],[c_775,c_209])).

tff(c_831,plain,(
    ! [A_114,B_115] : r1_tarski(k4_xboole_0(A_114,A_114),B_115) ),
    inference(resolution,[status(thm)],[c_775,c_209])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1012,plain,(
    ! [A_130,B_131] :
      ( k4_xboole_0(A_130,A_130) = B_131
      | ~ r1_tarski(B_131,k4_xboole_0(A_130,A_130)) ) ),
    inference(resolution,[status(thm)],[c_831,c_28])).

tff(c_1044,plain,(
    ! [A_133,A_132] : k4_xboole_0(A_133,A_133) = k4_xboole_0(A_132,A_132) ),
    inference(resolution,[status(thm)],[c_819,c_1012])).

tff(c_34,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1111,plain,(
    ! [A_132,A_133] : k4_xboole_0(A_132,k4_xboole_0(A_133,A_133)) = k3_xboole_0(A_132,A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_34])).

tff(c_1143,plain,(
    ! [A_132,A_133] : k4_xboole_0(A_132,k4_xboole_0(A_133,A_133)) = A_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1111])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_825,plain,(
    ! [A_111,B_112] : r1_tarski(k4_xboole_0(A_111,B_112),A_111) ),
    inference(resolution,[status(thm)],[c_775,c_4])).

tff(c_48,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_258,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_625,plain,(
    ! [A_91,B_92,B_93] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_93)
      | ~ r1_tarski(A_91,B_93)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35821,plain,(
    ! [A_557,B_558,B_559,B_560] :
      ( r2_hidden('#skF_1'(A_557,B_558),B_559)
      | ~ r1_tarski(B_560,B_559)
      | ~ r1_tarski(A_557,B_560)
      | r1_tarski(A_557,B_558) ) ),
    inference(resolution,[status(thm)],[c_625,c_2])).

tff(c_35890,plain,(
    ! [A_561,B_562] :
      ( r2_hidden('#skF_1'(A_561,B_562),k2_relat_1('#skF_5'))
      | ~ r1_tarski(A_561,'#skF_4')
      | r1_tarski(A_561,B_562) ) ),
    inference(resolution,[status(thm)],[c_48,c_35821])).

tff(c_36175,plain,(
    ! [A_568,B_569] :
      ( ~ r1_tarski(k4_xboole_0(A_568,k2_relat_1('#skF_5')),'#skF_4')
      | r1_tarski(k4_xboole_0(A_568,k2_relat_1('#skF_5')),B_569) ) ),
    inference(resolution,[status(thm)],[c_35890,c_209])).

tff(c_36304,plain,(
    ! [B_570] : r1_tarski(k4_xboole_0('#skF_4',k2_relat_1('#skF_5')),B_570) ),
    inference(resolution,[status(thm)],[c_825,c_36175])).

tff(c_839,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,A_114) = B_115
      | ~ r1_tarski(B_115,k4_xboole_0(A_114,A_114)) ) ),
    inference(resolution,[status(thm)],[c_831,c_28])).

tff(c_1058,plain,(
    ! [A_133,B_115,A_132] :
      ( k4_xboole_0(A_133,A_133) = B_115
      | ~ r1_tarski(B_115,k4_xboole_0(A_132,A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_839])).

tff(c_36393,plain,(
    ! [A_571] : k4_xboole_0(A_571,A_571) = k4_xboole_0('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36304,c_1058])).

tff(c_36914,plain,(
    ! [A_571] : k4_xboole_0('#skF_4',k4_xboole_0(A_571,A_571)) = k3_xboole_0('#skF_4',k2_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36393,c_34])).

tff(c_37073,plain,(
    k3_xboole_0('#skF_4',k2_relat_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_36914])).

tff(c_271,plain,(
    ! [B_67,A_68] :
      ( k3_xboole_0(k2_relat_1(B_67),A_68) = k2_relat_1(k8_relat_1(A_68,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_119,plain,(
    ! [B_37,A_38] : k1_setfam_1(k2_tarski(B_37,A_38)) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_104])).

tff(c_42,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_125,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_42])).

tff(c_283,plain,(
    ! [A_68,B_67] :
      ( k3_xboole_0(A_68,k2_relat_1(B_67)) = k2_relat_1(k8_relat_1(A_68,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_125])).

tff(c_37125,plain,
    ( k2_relat_1(k8_relat_1('#skF_4','#skF_5')) = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37073,c_283])).

tff(c_37160,plain,(
    k2_relat_1(k8_relat_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_37125])).

tff(c_37162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_37160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.64/6.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.64/6.89  
% 14.64/6.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.64/6.89  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 14.64/6.89  
% 14.64/6.89  %Foreground sorts:
% 14.64/6.89  
% 14.64/6.89  
% 14.64/6.89  %Background operators:
% 14.64/6.89  
% 14.64/6.89  
% 14.64/6.89  %Foreground operators:
% 14.64/6.89  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 14.64/6.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.64/6.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.64/6.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.64/6.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.64/6.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.64/6.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.64/6.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.64/6.89  tff('#skF_5', type, '#skF_5': $i).
% 14.64/6.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.64/6.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.64/6.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.64/6.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.64/6.89  tff('#skF_4', type, '#skF_4': $i).
% 14.64/6.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.64/6.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.64/6.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.64/6.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.64/6.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.64/6.89  
% 14.64/6.91  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 14.64/6.91  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.64/6.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.64/6.91  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.64/6.91  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.64/6.91  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.64/6.91  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 14.64/6.91  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.64/6.91  tff(f_60, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.64/6.91  tff(c_46, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.64/6.91  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.64/6.91  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.64/6.91  tff(c_195, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.64/6.91  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.64/6.91  tff(c_775, plain, (![A_111, B_112, B_113]: (r2_hidden('#skF_1'(k4_xboole_0(A_111, B_112), B_113), A_111) | r1_tarski(k4_xboole_0(A_111, B_112), B_113))), inference(resolution, [status(thm)], [c_195, c_12])).
% 14.64/6.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.64/6.91  tff(c_201, plain, (![D_48, B_49, A_50]: (~r2_hidden(D_48, B_49) | ~r2_hidden(D_48, k4_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.64/6.91  tff(c_209, plain, (![A_50, B_49, B_2]: (~r2_hidden('#skF_1'(k4_xboole_0(A_50, B_49), B_2), B_49) | r1_tarski(k4_xboole_0(A_50, B_49), B_2))), inference(resolution, [status(thm)], [c_6, c_201])).
% 14.64/6.91  tff(c_819, plain, (![A_111, B_113]: (r1_tarski(k4_xboole_0(A_111, A_111), B_113))), inference(resolution, [status(thm)], [c_775, c_209])).
% 14.64/6.91  tff(c_831, plain, (![A_114, B_115]: (r1_tarski(k4_xboole_0(A_114, A_114), B_115))), inference(resolution, [status(thm)], [c_775, c_209])).
% 14.64/6.91  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.64/6.91  tff(c_1012, plain, (![A_130, B_131]: (k4_xboole_0(A_130, A_130)=B_131 | ~r1_tarski(B_131, k4_xboole_0(A_130, A_130)))), inference(resolution, [status(thm)], [c_831, c_28])).
% 14.64/6.91  tff(c_1044, plain, (![A_133, A_132]: (k4_xboole_0(A_133, A_133)=k4_xboole_0(A_132, A_132))), inference(resolution, [status(thm)], [c_819, c_1012])).
% 14.64/6.91  tff(c_34, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.64/6.91  tff(c_1111, plain, (![A_132, A_133]: (k4_xboole_0(A_132, k4_xboole_0(A_133, A_133))=k3_xboole_0(A_132, A_132))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_34])).
% 14.64/6.91  tff(c_1143, plain, (![A_132, A_133]: (k4_xboole_0(A_132, k4_xboole_0(A_133, A_133))=A_132)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1111])).
% 14.64/6.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.64/6.91  tff(c_825, plain, (![A_111, B_112]: (r1_tarski(k4_xboole_0(A_111, B_112), A_111))), inference(resolution, [status(thm)], [c_775, c_4])).
% 14.64/6.91  tff(c_48, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.64/6.91  tff(c_258, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.64/6.91  tff(c_625, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_1'(A_91, B_92), B_93) | ~r1_tarski(A_91, B_93) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_6, c_258])).
% 14.64/6.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.64/6.91  tff(c_35821, plain, (![A_557, B_558, B_559, B_560]: (r2_hidden('#skF_1'(A_557, B_558), B_559) | ~r1_tarski(B_560, B_559) | ~r1_tarski(A_557, B_560) | r1_tarski(A_557, B_558))), inference(resolution, [status(thm)], [c_625, c_2])).
% 14.64/6.91  tff(c_35890, plain, (![A_561, B_562]: (r2_hidden('#skF_1'(A_561, B_562), k2_relat_1('#skF_5')) | ~r1_tarski(A_561, '#skF_4') | r1_tarski(A_561, B_562))), inference(resolution, [status(thm)], [c_48, c_35821])).
% 14.64/6.91  tff(c_36175, plain, (![A_568, B_569]: (~r1_tarski(k4_xboole_0(A_568, k2_relat_1('#skF_5')), '#skF_4') | r1_tarski(k4_xboole_0(A_568, k2_relat_1('#skF_5')), B_569))), inference(resolution, [status(thm)], [c_35890, c_209])).
% 14.64/6.91  tff(c_36304, plain, (![B_570]: (r1_tarski(k4_xboole_0('#skF_4', k2_relat_1('#skF_5')), B_570))), inference(resolution, [status(thm)], [c_825, c_36175])).
% 14.64/6.91  tff(c_839, plain, (![A_114, B_115]: (k4_xboole_0(A_114, A_114)=B_115 | ~r1_tarski(B_115, k4_xboole_0(A_114, A_114)))), inference(resolution, [status(thm)], [c_831, c_28])).
% 14.64/6.91  tff(c_1058, plain, (![A_133, B_115, A_132]: (k4_xboole_0(A_133, A_133)=B_115 | ~r1_tarski(B_115, k4_xboole_0(A_132, A_132)))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_839])).
% 14.64/6.91  tff(c_36393, plain, (![A_571]: (k4_xboole_0(A_571, A_571)=k4_xboole_0('#skF_4', k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_36304, c_1058])).
% 14.64/6.91  tff(c_36914, plain, (![A_571]: (k4_xboole_0('#skF_4', k4_xboole_0(A_571, A_571))=k3_xboole_0('#skF_4', k2_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_36393, c_34])).
% 14.64/6.91  tff(c_37073, plain, (k3_xboole_0('#skF_4', k2_relat_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_36914])).
% 14.64/6.91  tff(c_271, plain, (![B_67, A_68]: (k3_xboole_0(k2_relat_1(B_67), A_68)=k2_relat_1(k8_relat_1(A_68, B_67)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.64/6.91  tff(c_36, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.64/6.91  tff(c_104, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.64/6.91  tff(c_119, plain, (![B_37, A_38]: (k1_setfam_1(k2_tarski(B_37, A_38))=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_36, c_104])).
% 14.64/6.91  tff(c_42, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.64/6.91  tff(c_125, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_119, c_42])).
% 14.64/6.91  tff(c_283, plain, (![A_68, B_67]: (k3_xboole_0(A_68, k2_relat_1(B_67))=k2_relat_1(k8_relat_1(A_68, B_67)) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_271, c_125])).
% 14.64/6.91  tff(c_37125, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))='#skF_4' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_37073, c_283])).
% 14.64/6.91  tff(c_37160, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_37125])).
% 14.64/6.91  tff(c_37162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_37160])).
% 14.64/6.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.64/6.91  
% 14.64/6.91  Inference rules
% 14.64/6.91  ----------------------
% 14.64/6.91  #Ref     : 0
% 14.64/6.91  #Sup     : 10698
% 14.64/6.91  #Fact    : 0
% 14.64/6.91  #Define  : 0
% 14.64/6.91  #Split   : 1
% 14.64/6.91  #Chain   : 0
% 14.64/6.91  #Close   : 0
% 14.64/6.91  
% 14.64/6.91  Ordering : KBO
% 14.64/6.91  
% 14.64/6.91  Simplification rules
% 14.64/6.91  ----------------------
% 14.64/6.91  #Subsume      : 3014
% 14.64/6.91  #Demod        : 5142
% 14.64/6.91  #Tautology    : 2510
% 14.64/6.91  #SimpNegUnit  : 1
% 14.64/6.91  #BackRed      : 1
% 14.64/6.91  
% 14.64/6.91  #Partial instantiations: 0
% 14.64/6.91  #Strategies tried      : 1
% 14.64/6.91  
% 14.64/6.91  Timing (in seconds)
% 14.64/6.91  ----------------------
% 14.64/6.91  Preprocessing        : 0.31
% 14.64/6.91  Parsing              : 0.16
% 14.64/6.91  CNF conversion       : 0.02
% 14.64/6.91  Main loop            : 5.84
% 14.64/6.91  Inferencing          : 1.04
% 14.64/6.91  Reduction            : 2.97
% 14.64/6.91  Demodulation         : 2.66
% 14.64/6.91  BG Simplification    : 0.15
% 14.64/6.91  Subsumption          : 1.38
% 14.64/6.91  Abstraction          : 0.21
% 14.64/6.91  MUC search           : 0.00
% 14.64/6.91  Cooper               : 0.00
% 14.64/6.91  Total                : 6.18
% 14.64/6.91  Index Insertion      : 0.00
% 14.64/6.91  Index Deletion       : 0.00
% 14.64/6.91  Index Matching       : 0.00
% 14.64/6.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
