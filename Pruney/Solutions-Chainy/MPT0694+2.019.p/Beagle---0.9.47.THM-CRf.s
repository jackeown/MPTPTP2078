%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:55 EST 2020

% Result     : Theorem 18.73s
% Output     : CNFRefutation 18.73s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 198 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46597,plain,(
    ! [C_1643,A_1644,B_1645] :
      ( r1_tarski(k9_relat_1(C_1643,k3_xboole_0(A_1644,B_1645)),k3_xboole_0(k9_relat_1(C_1643,A_1644),k9_relat_1(C_1643,B_1645)))
      | ~ v1_relat_1(C_1643) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46965,plain,(
    ! [C_1672,A_1673,B_1674] :
      ( r1_tarski(k9_relat_1(C_1672,k3_xboole_0(A_1673,B_1674)),k9_relat_1(C_1672,A_1673))
      | ~ v1_relat_1(C_1672) ) ),
    inference(resolution,[status(thm)],[c_46597,c_4])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_30,B_31] :
      ( v1_funct_1(k7_relat_1(A_30,B_31))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_403,plain,(
    ! [A_91,C_92,B_93] :
      ( k3_xboole_0(A_91,k10_relat_1(C_92,B_93)) = k10_relat_1(k7_relat_1(C_92,A_91),B_93)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_56,B_57] : r1_tarski(k3_xboole_0(A_56,B_57),A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_8])).

tff(c_445,plain,(
    ! [C_92,A_91,B_93] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_92,A_91),B_93),A_91)
      | ~ v1_relat_1(C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_147])).

tff(c_649,plain,(
    ! [A_113,C_114,B_115] :
      ( k9_relat_1(k7_relat_1(A_113,C_114),B_115) = k9_relat_1(A_113,B_115)
      | ~ r1_tarski(B_115,C_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [B_36,A_35] :
      ( r1_tarski(k9_relat_1(B_36,k10_relat_1(B_36,A_35)),A_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3413,plain,(
    ! [A_321,C_322,A_323] :
      ( r1_tarski(k9_relat_1(A_321,k10_relat_1(k7_relat_1(A_321,C_322),A_323)),A_323)
      | ~ v1_funct_1(k7_relat_1(A_321,C_322))
      | ~ v1_relat_1(k7_relat_1(A_321,C_322))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_321,C_322),A_323),C_322)
      | ~ v1_relat_1(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_30])).

tff(c_46366,plain,(
    ! [C_1625,A_1626,B_1627] :
      ( r1_tarski(k9_relat_1(C_1625,k10_relat_1(k7_relat_1(C_1625,A_1626),B_1627)),B_1627)
      | ~ v1_funct_1(k7_relat_1(C_1625,A_1626))
      | ~ v1_relat_1(k7_relat_1(C_1625,A_1626))
      | ~ v1_relat_1(C_1625) ) ),
    inference(resolution,[status(thm)],[c_445,c_3413])).

tff(c_28,plain,(
    ! [A_32,C_34,B_33] :
      ( k3_xboole_0(A_32,k10_relat_1(C_34,B_33)) = k10_relat_1(k7_relat_1(C_34,A_32),B_33)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_293,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k3_xboole_0(B_82,C_83))
      | ~ r1_tarski(A_81,C_83)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_37,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_306,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_293,c_37])).

tff(c_562,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_565,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_562])).

tff(c_567,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_565])).

tff(c_46391,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46366,c_567])).

tff(c_46418,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46391])).

tff(c_46421,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46418])).

tff(c_46424,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_46421])).

tff(c_46428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46424])).

tff(c_46429,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46418])).

tff(c_46433,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_46429])).

tff(c_46437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_46433])).

tff(c_46438,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_46968,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46965,c_46438])).

tff(c_46988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.73/10.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.73/10.36  
% 18.73/10.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.73/10.37  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 18.73/10.37  
% 18.73/10.37  %Foreground sorts:
% 18.73/10.37  
% 18.73/10.37  
% 18.73/10.37  %Background operators:
% 18.73/10.37  
% 18.73/10.37  
% 18.73/10.37  %Foreground operators:
% 18.73/10.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.73/10.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.73/10.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.73/10.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.73/10.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.73/10.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.73/10.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.73/10.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.73/10.37  tff('#skF_2', type, '#skF_2': $i).
% 18.73/10.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.73/10.37  tff('#skF_3', type, '#skF_3': $i).
% 18.73/10.37  tff('#skF_1', type, '#skF_1': $i).
% 18.73/10.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.73/10.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.73/10.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.73/10.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.73/10.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.73/10.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.73/10.37  
% 18.73/10.38  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 18.73/10.38  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 18.73/10.38  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 18.73/10.38  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 18.73/10.38  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 18.73/10.38  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 18.73/10.38  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.73/10.38  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 18.73/10.38  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 18.73/10.38  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 18.73/10.38  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 18.73/10.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.73/10.38  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.73/10.38  tff(c_46597, plain, (![C_1643, A_1644, B_1645]: (r1_tarski(k9_relat_1(C_1643, k3_xboole_0(A_1644, B_1645)), k3_xboole_0(k9_relat_1(C_1643, A_1644), k9_relat_1(C_1643, B_1645))) | ~v1_relat_1(C_1643))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.73/10.38  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.73/10.38  tff(c_46965, plain, (![C_1672, A_1673, B_1674]: (r1_tarski(k9_relat_1(C_1672, k3_xboole_0(A_1673, B_1674)), k9_relat_1(C_1672, A_1673)) | ~v1_relat_1(C_1672))), inference(resolution, [status(thm)], [c_46597, c_4])).
% 18.73/10.38  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.73/10.38  tff(c_24, plain, (![A_30, B_31]: (v1_funct_1(k7_relat_1(A_30, B_31)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.73/10.38  tff(c_18, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.73/10.38  tff(c_403, plain, (![A_91, C_92, B_93]: (k3_xboole_0(A_91, k10_relat_1(C_92, B_93))=k10_relat_1(k7_relat_1(C_92, A_91), B_93) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.73/10.38  tff(c_130, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.73/10.38  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.73/10.38  tff(c_147, plain, (![A_56, B_57]: (r1_tarski(k3_xboole_0(A_56, B_57), A_56))), inference(superposition, [status(thm), theory('equality')], [c_130, c_8])).
% 18.73/10.38  tff(c_445, plain, (![C_92, A_91, B_93]: (r1_tarski(k10_relat_1(k7_relat_1(C_92, A_91), B_93), A_91) | ~v1_relat_1(C_92))), inference(superposition, [status(thm), theory('equality')], [c_403, c_147])).
% 18.73/10.38  tff(c_649, plain, (![A_113, C_114, B_115]: (k9_relat_1(k7_relat_1(A_113, C_114), B_115)=k9_relat_1(A_113, B_115) | ~r1_tarski(B_115, C_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.73/10.38  tff(c_30, plain, (![B_36, A_35]: (r1_tarski(k9_relat_1(B_36, k10_relat_1(B_36, A_35)), A_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.73/10.38  tff(c_3413, plain, (![A_321, C_322, A_323]: (r1_tarski(k9_relat_1(A_321, k10_relat_1(k7_relat_1(A_321, C_322), A_323)), A_323) | ~v1_funct_1(k7_relat_1(A_321, C_322)) | ~v1_relat_1(k7_relat_1(A_321, C_322)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_321, C_322), A_323), C_322) | ~v1_relat_1(A_321))), inference(superposition, [status(thm), theory('equality')], [c_649, c_30])).
% 18.73/10.38  tff(c_46366, plain, (![C_1625, A_1626, B_1627]: (r1_tarski(k9_relat_1(C_1625, k10_relat_1(k7_relat_1(C_1625, A_1626), B_1627)), B_1627) | ~v1_funct_1(k7_relat_1(C_1625, A_1626)) | ~v1_relat_1(k7_relat_1(C_1625, A_1626)) | ~v1_relat_1(C_1625))), inference(resolution, [status(thm)], [c_445, c_3413])).
% 18.73/10.38  tff(c_28, plain, (![A_32, C_34, B_33]: (k3_xboole_0(A_32, k10_relat_1(C_34, B_33))=k10_relat_1(k7_relat_1(C_34, A_32), B_33) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.73/10.38  tff(c_293, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k3_xboole_0(B_82, C_83)) | ~r1_tarski(A_81, C_83) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.73/10.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.73/10.38  tff(c_32, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.73/10.38  tff(c_37, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 18.73/10.38  tff(c_306, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_293, c_37])).
% 18.73/10.38  tff(c_562, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_306])).
% 18.73/10.38  tff(c_565, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_562])).
% 18.73/10.38  tff(c_567, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_565])).
% 18.73/10.38  tff(c_46391, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46366, c_567])).
% 18.73/10.38  tff(c_46418, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46391])).
% 18.73/10.38  tff(c_46421, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_46418])).
% 18.73/10.38  tff(c_46424, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_46421])).
% 18.73/10.38  tff(c_46428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_46424])).
% 18.73/10.38  tff(c_46429, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_46418])).
% 18.73/10.38  tff(c_46433, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_46429])).
% 18.73/10.38  tff(c_46437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_46433])).
% 18.73/10.38  tff(c_46438, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_306])).
% 18.73/10.38  tff(c_46968, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46965, c_46438])).
% 18.73/10.38  tff(c_46988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_46968])).
% 18.73/10.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.73/10.38  
% 18.73/10.38  Inference rules
% 18.73/10.38  ----------------------
% 18.73/10.38  #Ref     : 0
% 18.73/10.38  #Sup     : 11039
% 18.73/10.38  #Fact    : 0
% 18.73/10.38  #Define  : 0
% 18.73/10.38  #Split   : 2
% 18.73/10.38  #Chain   : 0
% 18.73/10.38  #Close   : 0
% 18.73/10.38  
% 18.73/10.38  Ordering : KBO
% 18.73/10.38  
% 18.73/10.38  Simplification rules
% 18.73/10.38  ----------------------
% 18.73/10.38  #Subsume      : 1369
% 18.73/10.38  #Demod        : 5328
% 18.73/10.38  #Tautology    : 4218
% 18.73/10.38  #SimpNegUnit  : 0
% 18.73/10.38  #BackRed      : 0
% 18.73/10.38  
% 18.73/10.38  #Partial instantiations: 0
% 18.73/10.38  #Strategies tried      : 1
% 18.73/10.38  
% 18.73/10.38  Timing (in seconds)
% 18.73/10.38  ----------------------
% 18.73/10.38  Preprocessing        : 0.30
% 18.73/10.38  Parsing              : 0.16
% 18.73/10.38  CNF conversion       : 0.02
% 18.73/10.38  Main loop            : 9.30
% 18.73/10.38  Inferencing          : 1.36
% 18.73/10.38  Reduction            : 4.76
% 18.73/10.38  Demodulation         : 4.37
% 18.73/10.38  BG Simplification    : 0.13
% 18.73/10.38  Subsumption          : 2.65
% 18.73/10.38  Abstraction          : 0.15
% 18.73/10.38  MUC search           : 0.00
% 18.73/10.38  Cooper               : 0.00
% 18.73/10.38  Total                : 9.63
% 18.73/10.38  Index Insertion      : 0.00
% 18.73/10.38  Index Deletion       : 0.00
% 18.73/10.38  Index Matching       : 0.00
% 18.73/10.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
