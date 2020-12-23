%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:55 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 192 expanded)
%              Number of equality atoms :    7 (  18 expanded)
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

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6876,plain,(
    ! [C_574,A_575,B_576] :
      ( r1_tarski(k9_relat_1(C_574,k3_xboole_0(A_575,B_576)),k3_xboole_0(k9_relat_1(C_574,A_575),k9_relat_1(C_574,B_576)))
      | ~ v1_relat_1(C_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k3_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6965,plain,(
    ! [C_581,A_582,B_583] :
      ( r1_tarski(k9_relat_1(C_581,k3_xboole_0(A_582,B_583)),k9_relat_1(C_581,A_582))
      | ~ v1_relat_1(C_581) ) ),
    inference(resolution,[status(thm)],[c_6876,c_6])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_28,B_29] :
      ( v1_funct_1(k7_relat_1(A_28,B_29))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_473,plain,(
    ! [A_95,C_96,B_97] :
      ( k3_xboole_0(A_95,k10_relat_1(C_96,B_97)) = k10_relat_1(k7_relat_1(C_96,A_95),B_97)
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_563,plain,(
    ! [C_96,A_95,B_97] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_96,A_95),B_97),A_95)
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_4])).

tff(c_644,plain,(
    ! [A_105,C_106,B_107] :
      ( k9_relat_1(k7_relat_1(A_105,C_106),B_107) = k9_relat_1(A_105,B_107)
      | ~ r1_tarski(B_107,C_106)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k9_relat_1(B_34,k10_relat_1(B_34,A_33)),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2794,plain,(
    ! [A_291,C_292,A_293] :
      ( r1_tarski(k9_relat_1(A_291,k10_relat_1(k7_relat_1(A_291,C_292),A_293)),A_293)
      | ~ v1_funct_1(k7_relat_1(A_291,C_292))
      | ~ v1_relat_1(k7_relat_1(A_291,C_292))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_291,C_292),A_293),C_292)
      | ~ v1_relat_1(A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_28])).

tff(c_6704,plain,(
    ! [C_560,A_561,B_562] :
      ( r1_tarski(k9_relat_1(C_560,k10_relat_1(k7_relat_1(C_560,A_561),B_562)),B_562)
      | ~ v1_funct_1(k7_relat_1(C_560,A_561))
      | ~ v1_relat_1(k7_relat_1(C_560,A_561))
      | ~ v1_relat_1(C_560) ) ),
    inference(resolution,[status(thm)],[c_563,c_2794])).

tff(c_26,plain,(
    ! [A_30,C_32,B_31] :
      ( k3_xboole_0(A_30,k10_relat_1(C_32,B_31)) = k10_relat_1(k7_relat_1(C_32,A_30),B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_379,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(A_84,k3_xboole_0(B_85,C_86))
      | ~ r1_tarski(A_84,C_86)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_397,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_379,c_35])).

tff(c_592,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_595,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_592])).

tff(c_597,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_595])).

tff(c_6715,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6704,c_597])).

tff(c_6738,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6715])).

tff(c_6741,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6738])).

tff(c_6744,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_6741])).

tff(c_6748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6744])).

tff(c_6749,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6738])).

tff(c_6753,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_6749])).

tff(c_6757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_6753])).

tff(c_6758,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_6968,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6965,c_6758])).

tff(c_6988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.64  
% 7.23/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.64  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 7.23/2.64  
% 7.23/2.64  %Foreground sorts:
% 7.23/2.64  
% 7.23/2.64  
% 7.23/2.64  %Background operators:
% 7.23/2.64  
% 7.23/2.64  
% 7.23/2.64  %Foreground operators:
% 7.23/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.23/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.23/2.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.23/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.23/2.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.23/2.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.23/2.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.23/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.23/2.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.23/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.23/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.23/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.23/2.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.23/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.23/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.23/2.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.23/2.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.23/2.64  
% 7.23/2.65  tff(f_85, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 7.23/2.65  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 7.23/2.65  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 7.23/2.65  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 7.23/2.65  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.23/2.65  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 7.23/2.65  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.23/2.65  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 7.23/2.65  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 7.23/2.65  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 7.23/2.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.23/2.65  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.23/2.65  tff(c_6876, plain, (![C_574, A_575, B_576]: (r1_tarski(k9_relat_1(C_574, k3_xboole_0(A_575, B_576)), k3_xboole_0(k9_relat_1(C_574, A_575), k9_relat_1(C_574, B_576))) | ~v1_relat_1(C_574))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.23/2.65  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.23/2.65  tff(c_6965, plain, (![C_581, A_582, B_583]: (r1_tarski(k9_relat_1(C_581, k3_xboole_0(A_582, B_583)), k9_relat_1(C_581, A_582)) | ~v1_relat_1(C_581))), inference(resolution, [status(thm)], [c_6876, c_6])).
% 7.23/2.65  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.23/2.65  tff(c_22, plain, (![A_28, B_29]: (v1_funct_1(k7_relat_1(A_28, B_29)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.23/2.65  tff(c_16, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.23/2.65  tff(c_473, plain, (![A_95, C_96, B_97]: (k3_xboole_0(A_95, k10_relat_1(C_96, B_97))=k10_relat_1(k7_relat_1(C_96, A_95), B_97) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.23/2.65  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.23/2.65  tff(c_563, plain, (![C_96, A_95, B_97]: (r1_tarski(k10_relat_1(k7_relat_1(C_96, A_95), B_97), A_95) | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_473, c_4])).
% 7.23/2.65  tff(c_644, plain, (![A_105, C_106, B_107]: (k9_relat_1(k7_relat_1(A_105, C_106), B_107)=k9_relat_1(A_105, B_107) | ~r1_tarski(B_107, C_106) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.23/2.65  tff(c_28, plain, (![B_34, A_33]: (r1_tarski(k9_relat_1(B_34, k10_relat_1(B_34, A_33)), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.23/2.65  tff(c_2794, plain, (![A_291, C_292, A_293]: (r1_tarski(k9_relat_1(A_291, k10_relat_1(k7_relat_1(A_291, C_292), A_293)), A_293) | ~v1_funct_1(k7_relat_1(A_291, C_292)) | ~v1_relat_1(k7_relat_1(A_291, C_292)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_291, C_292), A_293), C_292) | ~v1_relat_1(A_291))), inference(superposition, [status(thm), theory('equality')], [c_644, c_28])).
% 7.23/2.65  tff(c_6704, plain, (![C_560, A_561, B_562]: (r1_tarski(k9_relat_1(C_560, k10_relat_1(k7_relat_1(C_560, A_561), B_562)), B_562) | ~v1_funct_1(k7_relat_1(C_560, A_561)) | ~v1_relat_1(k7_relat_1(C_560, A_561)) | ~v1_relat_1(C_560))), inference(resolution, [status(thm)], [c_563, c_2794])).
% 7.23/2.65  tff(c_26, plain, (![A_30, C_32, B_31]: (k3_xboole_0(A_30, k10_relat_1(C_32, B_31))=k10_relat_1(k7_relat_1(C_32, A_30), B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.23/2.65  tff(c_379, plain, (![A_84, B_85, C_86]: (r1_tarski(A_84, k3_xboole_0(B_85, C_86)) | ~r1_tarski(A_84, C_86) | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.23/2.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.23/2.65  tff(c_30, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.23/2.65  tff(c_35, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 7.23/2.65  tff(c_397, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_379, c_35])).
% 7.23/2.65  tff(c_592, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_397])).
% 7.23/2.65  tff(c_595, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_592])).
% 7.23/2.65  tff(c_597, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_595])).
% 7.23/2.65  tff(c_6715, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6704, c_597])).
% 7.23/2.65  tff(c_6738, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6715])).
% 7.23/2.65  tff(c_6741, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6738])).
% 7.23/2.65  tff(c_6744, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_6741])).
% 7.23/2.65  tff(c_6748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6744])).
% 7.23/2.65  tff(c_6749, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_6738])).
% 7.23/2.65  tff(c_6753, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_6749])).
% 7.23/2.65  tff(c_6757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_6753])).
% 7.23/2.65  tff(c_6758, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_397])).
% 7.23/2.65  tff(c_6968, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6965, c_6758])).
% 7.23/2.65  tff(c_6988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6968])).
% 7.23/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.65  
% 7.23/2.65  Inference rules
% 7.23/2.65  ----------------------
% 7.23/2.65  #Ref     : 0
% 7.23/2.65  #Sup     : 1609
% 7.23/2.65  #Fact    : 0
% 7.23/2.65  #Define  : 0
% 7.23/2.65  #Split   : 2
% 7.23/2.65  #Chain   : 0
% 7.23/2.65  #Close   : 0
% 7.23/2.65  
% 7.23/2.65  Ordering : KBO
% 7.23/2.65  
% 7.23/2.65  Simplification rules
% 7.23/2.65  ----------------------
% 7.23/2.65  #Subsume      : 165
% 7.23/2.65  #Demod        : 484
% 7.23/2.65  #Tautology    : 507
% 7.23/2.65  #SimpNegUnit  : 0
% 7.23/2.65  #BackRed      : 0
% 7.23/2.65  
% 7.23/2.65  #Partial instantiations: 0
% 7.23/2.65  #Strategies tried      : 1
% 7.23/2.65  
% 7.23/2.65  Timing (in seconds)
% 7.23/2.65  ----------------------
% 7.23/2.65  Preprocessing        : 0.31
% 7.23/2.65  Parsing              : 0.17
% 7.23/2.65  CNF conversion       : 0.02
% 7.23/2.65  Main loop            : 1.56
% 7.23/2.65  Inferencing          : 0.40
% 7.23/2.65  Reduction            : 0.64
% 7.23/2.65  Demodulation         : 0.55
% 7.23/2.65  BG Simplification    : 0.05
% 7.23/2.65  Subsumption          : 0.38
% 7.23/2.65  Abstraction          : 0.04
% 7.23/2.65  MUC search           : 0.00
% 7.23/2.65  Cooper               : 0.00
% 7.23/2.65  Total                : 1.89
% 7.23/2.65  Index Insertion      : 0.00
% 7.23/2.65  Index Deletion       : 0.00
% 7.23/2.65  Index Matching       : 0.00
% 7.23/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
