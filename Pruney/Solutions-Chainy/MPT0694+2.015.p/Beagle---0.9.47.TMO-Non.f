%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:55 EST 2020

% Result     : Timeout 57.64s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   64 ( 117 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 206 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_186580,plain,(
    ! [C_1223,A_1224,B_1225] :
      ( r1_tarski(k9_relat_1(C_1223,k3_xboole_0(A_1224,B_1225)),k3_xboole_0(k9_relat_1(C_1223,A_1224),k9_relat_1(C_1223,B_1225)))
      | ~ v1_relat_1(C_1223) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k3_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_187001,plain,(
    ! [C_1230,A_1231,B_1232] :
      ( r1_tarski(k9_relat_1(C_1230,k3_xboole_0(A_1231,B_1232)),k9_relat_1(C_1230,A_1231))
      | ~ v1_relat_1(C_1230) ) ),
    inference(resolution,[status(thm)],[c_186580,c_10])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [A_28,B_29] :
      ( v1_funct_1(k7_relat_1(A_28,B_29))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_772,plain,(
    ! [A_89,C_90,B_91] :
      ( k3_xboole_0(A_89,k10_relat_1(C_90,B_91)) = k10_relat_1(k7_relat_1(C_90,A_89),B_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,B_47)
      | ~ r1_tarski(A_46,k3_xboole_0(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_47,C_48] : r1_tarski(k3_xboole_0(B_47,C_48),B_47) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_831,plain,(
    ! [C_90,A_89,B_91] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_90,A_89),B_91),A_89)
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_112])).

tff(c_1243,plain,(
    ! [A_98,C_99,B_100] :
      ( k9_relat_1(k7_relat_1(A_98,C_99),B_100) = k9_relat_1(A_98,B_100)
      | ~ r1_tarski(B_100,C_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k9_relat_1(B_34,k10_relat_1(B_34,A_33)),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7417,plain,(
    ! [A_238,C_239,A_240] :
      ( r1_tarski(k9_relat_1(A_238,k10_relat_1(k7_relat_1(A_238,C_239),A_240)),A_240)
      | ~ v1_funct_1(k7_relat_1(A_238,C_239))
      | ~ v1_relat_1(k7_relat_1(A_238,C_239))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_238,C_239),A_240),C_239)
      | ~ v1_relat_1(A_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_32])).

tff(c_185839,plain,(
    ! [C_1211,A_1212,B_1213] :
      ( r1_tarski(k9_relat_1(C_1211,k10_relat_1(k7_relat_1(C_1211,A_1212),B_1213)),B_1213)
      | ~ v1_funct_1(k7_relat_1(C_1211,A_1212))
      | ~ v1_relat_1(k7_relat_1(C_1211,A_1212))
      | ~ v1_relat_1(C_1211) ) ),
    inference(resolution,[status(thm)],[c_831,c_7417])).

tff(c_30,plain,(
    ! [A_30,C_32,B_31] :
      ( k3_xboole_0(A_30,k10_relat_1(C_32,B_31)) = k10_relat_1(k7_relat_1(C_32,A_30),B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_328,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(A_77,k3_xboole_0(B_78,C_79))
      | ~ r1_tarski(A_77,C_79)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_354,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_40])).

tff(c_994,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_1443,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_994])).

tff(c_1445,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1443])).

tff(c_186012,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185839,c_1445])).

tff(c_186092,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_186012])).

tff(c_186098,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_186092])).

tff(c_186101,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_186098])).

tff(c_186105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_186101])).

tff(c_186106,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_186092])).

tff(c_186110,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_186106])).

tff(c_186114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_186110])).

tff(c_186115,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_187004,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187001,c_186115])).

tff(c_187056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_187004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:17:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 57.64/47.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 57.64/47.18  
% 57.64/47.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 57.64/47.18  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 57.64/47.18  
% 57.64/47.18  %Foreground sorts:
% 57.64/47.18  
% 57.64/47.18  
% 57.64/47.18  %Background operators:
% 57.64/47.18  
% 57.64/47.18  
% 57.64/47.18  %Foreground operators:
% 57.64/47.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 57.64/47.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 57.64/47.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 57.64/47.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 57.64/47.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 57.64/47.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 57.64/47.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 57.64/47.18  tff('#skF_2', type, '#skF_2': $i).
% 57.64/47.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 57.64/47.18  tff('#skF_3', type, '#skF_3': $i).
% 57.64/47.18  tff('#skF_1', type, '#skF_1': $i).
% 57.64/47.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 57.64/47.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 57.64/47.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 57.64/47.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 57.64/47.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 57.64/47.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 57.64/47.18  
% 57.64/47.19  tff(f_89, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 57.64/47.19  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 57.64/47.19  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 57.64/47.19  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 57.64/47.19  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 57.64/47.19  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 57.64/47.19  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 57.64/47.19  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 57.64/47.19  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 57.64/47.19  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 57.64/47.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 57.64/47.19  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 57.64/47.19  tff(c_186580, plain, (![C_1223, A_1224, B_1225]: (r1_tarski(k9_relat_1(C_1223, k3_xboole_0(A_1224, B_1225)), k3_xboole_0(k9_relat_1(C_1223, A_1224), k9_relat_1(C_1223, B_1225))) | ~v1_relat_1(C_1223))), inference(cnfTransformation, [status(thm)], [f_57])).
% 57.64/47.19  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 57.64/47.19  tff(c_187001, plain, (![C_1230, A_1231, B_1232]: (r1_tarski(k9_relat_1(C_1230, k3_xboole_0(A_1231, B_1232)), k9_relat_1(C_1230, A_1231)) | ~v1_relat_1(C_1230))), inference(resolution, [status(thm)], [c_186580, c_10])).
% 57.64/47.19  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 57.64/47.19  tff(c_26, plain, (![A_28, B_29]: (v1_funct_1(k7_relat_1(A_28, B_29)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 57.64/47.19  tff(c_20, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 57.64/47.19  tff(c_772, plain, (![A_89, C_90, B_91]: (k3_xboole_0(A_89, k10_relat_1(C_90, B_91))=k10_relat_1(k7_relat_1(C_90, A_89), B_91) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_76])).
% 57.64/47.19  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 57.64/47.19  tff(c_101, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, B_47) | ~r1_tarski(A_46, k3_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 57.64/47.19  tff(c_112, plain, (![B_47, C_48]: (r1_tarski(k3_xboole_0(B_47, C_48), B_47))), inference(resolution, [status(thm)], [c_8, c_101])).
% 57.64/47.19  tff(c_831, plain, (![C_90, A_89, B_91]: (r1_tarski(k10_relat_1(k7_relat_1(C_90, A_89), B_91), A_89) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_772, c_112])).
% 57.64/47.19  tff(c_1243, plain, (![A_98, C_99, B_100]: (k9_relat_1(k7_relat_1(A_98, C_99), B_100)=k9_relat_1(A_98, B_100) | ~r1_tarski(B_100, C_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_64])).
% 57.64/47.19  tff(c_32, plain, (![B_34, A_33]: (r1_tarski(k9_relat_1(B_34, k10_relat_1(B_34, A_33)), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 57.64/47.19  tff(c_7417, plain, (![A_238, C_239, A_240]: (r1_tarski(k9_relat_1(A_238, k10_relat_1(k7_relat_1(A_238, C_239), A_240)), A_240) | ~v1_funct_1(k7_relat_1(A_238, C_239)) | ~v1_relat_1(k7_relat_1(A_238, C_239)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_238, C_239), A_240), C_239) | ~v1_relat_1(A_238))), inference(superposition, [status(thm), theory('equality')], [c_1243, c_32])).
% 57.64/47.19  tff(c_185839, plain, (![C_1211, A_1212, B_1213]: (r1_tarski(k9_relat_1(C_1211, k10_relat_1(k7_relat_1(C_1211, A_1212), B_1213)), B_1213) | ~v1_funct_1(k7_relat_1(C_1211, A_1212)) | ~v1_relat_1(k7_relat_1(C_1211, A_1212)) | ~v1_relat_1(C_1211))), inference(resolution, [status(thm)], [c_831, c_7417])).
% 57.64/47.19  tff(c_30, plain, (![A_30, C_32, B_31]: (k3_xboole_0(A_30, k10_relat_1(C_32, B_31))=k10_relat_1(k7_relat_1(C_32, A_30), B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_76])).
% 57.64/47.19  tff(c_328, plain, (![A_77, B_78, C_79]: (r1_tarski(A_77, k3_xboole_0(B_78, C_79)) | ~r1_tarski(A_77, C_79) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 57.64/47.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 57.64/47.19  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 57.64/47.19  tff(c_40, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 57.64/47.19  tff(c_354, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_328, c_40])).
% 57.64/47.19  tff(c_994, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_354])).
% 57.64/47.19  tff(c_1443, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_994])).
% 57.64/47.19  tff(c_1445, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1443])).
% 57.64/47.19  tff(c_186012, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185839, c_1445])).
% 57.64/47.19  tff(c_186092, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_186012])).
% 57.64/47.19  tff(c_186098, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_186092])).
% 57.64/47.19  tff(c_186101, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_186098])).
% 57.64/47.19  tff(c_186105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_186101])).
% 57.64/47.19  tff(c_186106, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_186092])).
% 57.64/47.19  tff(c_186110, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_186106])).
% 57.64/47.19  tff(c_186114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_186110])).
% 57.64/47.19  tff(c_186115, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_354])).
% 57.64/47.19  tff(c_187004, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_187001, c_186115])).
% 57.64/47.19  tff(c_187056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_187004])).
% 57.64/47.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 57.64/47.19  
% 57.64/47.19  Inference rules
% 57.64/47.19  ----------------------
% 57.64/47.19  #Ref     : 0
% 57.64/47.19  #Sup     : 48891
% 57.64/47.19  #Fact    : 0
% 57.64/47.19  #Define  : 0
% 57.64/47.19  #Split   : 3
% 57.64/47.19  #Chain   : 0
% 57.64/47.19  #Close   : 0
% 57.64/47.19  
% 57.64/47.19  Ordering : KBO
% 57.64/47.19  
% 57.64/47.19  Simplification rules
% 57.64/47.19  ----------------------
% 57.64/47.19  #Subsume      : 10559
% 57.64/47.19  #Demod        : 30384
% 57.64/47.19  #Tautology    : 10143
% 57.64/47.19  #SimpNegUnit  : 0
% 57.64/47.19  #BackRed      : 0
% 57.64/47.19  
% 57.64/47.19  #Partial instantiations: 0
% 57.64/47.19  #Strategies tried      : 1
% 57.64/47.19  
% 57.64/47.19  Timing (in seconds)
% 57.64/47.19  ----------------------
% 57.64/47.20  Preprocessing        : 0.31
% 57.64/47.20  Parsing              : 0.17
% 57.64/47.20  CNF conversion       : 0.02
% 57.64/47.20  Main loop            : 46.12
% 57.64/47.20  Inferencing          : 3.66
% 57.64/47.20  Reduction            : 27.50
% 57.64/47.20  Demodulation         : 26.14
% 57.64/47.20  BG Simplification    : 0.59
% 57.64/47.20  Subsumption          : 12.15
% 57.64/47.20  Abstraction          : 0.95
% 57.64/47.20  MUC search           : 0.00
% 57.64/47.20  Cooper               : 0.00
% 57.64/47.20  Total                : 46.46
% 57.64/47.20  Index Insertion      : 0.00
% 57.64/47.20  Index Deletion       : 0.00
% 57.64/47.20  Index Matching       : 0.00
% 57.64/47.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
