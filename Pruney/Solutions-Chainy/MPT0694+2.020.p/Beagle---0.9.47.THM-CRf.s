%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:55 EST 2020

% Result     : Theorem 8.32s
% Output     : CNFRefutation 8.32s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 120 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 200 expanded)
%              Number of equality atoms :    9 (  24 expanded)
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

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_90,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_46,B_47] : r1_tarski(k3_xboole_0(A_46,B_47),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_6])).

tff(c_18,plain,(
    ! [C_21,A_19,B_20] :
      ( r1_tarski(k9_relat_1(C_21,A_19),k9_relat_1(C_21,B_20))
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( v1_funct_1(k7_relat_1(A_27,B_28))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_204,plain,(
    ! [A_64,C_65,B_66] :
      ( k3_xboole_0(A_64,k10_relat_1(C_65,B_66)) = k10_relat_1(k7_relat_1(C_65,A_64),B_66)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_222,plain,(
    ! [C_65,A_64,B_66] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_65,A_64),B_66),A_64)
      | ~ v1_relat_1(C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_99])).

tff(c_296,plain,(
    ! [A_79,C_80,B_81] :
      ( k9_relat_1(k7_relat_1(A_79,C_80),B_81) = k9_relat_1(A_79,B_81)
      | ~ r1_tarski(B_81,C_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k9_relat_1(B_33,k10_relat_1(B_33,A_32)),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1423,plain,(
    ! [A_138,C_139,A_140] :
      ( r1_tarski(k9_relat_1(A_138,k10_relat_1(k7_relat_1(A_138,C_139),A_140)),A_140)
      | ~ v1_funct_1(k7_relat_1(A_138,C_139))
      | ~ v1_relat_1(k7_relat_1(A_138,C_139))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_138,C_139),A_140),C_139)
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_28])).

tff(c_6082,plain,(
    ! [C_237,A_238,B_239] :
      ( r1_tarski(k9_relat_1(C_237,k10_relat_1(k7_relat_1(C_237,A_238),B_239)),B_239)
      | ~ v1_funct_1(k7_relat_1(C_237,A_238))
      | ~ v1_relat_1(k7_relat_1(C_237,A_238))
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_222,c_1423])).

tff(c_26,plain,(
    ! [A_29,C_31,B_30] :
      ( k3_xboole_0(A_29,k10_relat_1(C_31,B_30)) = k10_relat_1(k7_relat_1(C_31,A_29),B_30)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(A_61,k3_xboole_0(B_62,C_63))
      | ~ r1_tarski(A_61,C_63)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_203,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_193,c_35])).

tff(c_315,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_318,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_320,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_318])).

tff(c_6085,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6082,c_320])).

tff(c_6098,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6085])).

tff(c_6099,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6098])).

tff(c_6102,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_6099])).

tff(c_6106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6102])).

tff(c_6107,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6098])).

tff(c_6111,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_6107])).

tff(c_6115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_6111])).

tff(c_6116,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_6125,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_6116])).

tff(c_6132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_99,c_6125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.32/3.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.32/3.26  
% 8.32/3.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.32/3.26  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.32/3.26  
% 8.32/3.26  %Foreground sorts:
% 8.32/3.26  
% 8.32/3.26  
% 8.32/3.26  %Background operators:
% 8.32/3.26  
% 8.32/3.26  
% 8.32/3.26  %Foreground operators:
% 8.32/3.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.32/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.32/3.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.32/3.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.32/3.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.32/3.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.32/3.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.32/3.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.32/3.26  tff('#skF_2', type, '#skF_2': $i).
% 8.32/3.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.32/3.26  tff('#skF_3', type, '#skF_3': $i).
% 8.32/3.26  tff('#skF_1', type, '#skF_1': $i).
% 8.32/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.32/3.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.32/3.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.32/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.32/3.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.32/3.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.32/3.26  
% 8.32/3.27  tff(f_85, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 8.32/3.27  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.32/3.27  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.32/3.27  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 8.32/3.27  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 8.32/3.27  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.32/3.27  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 8.32/3.27  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 8.32/3.27  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 8.32/3.27  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 8.32/3.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.32/3.27  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.32/3.27  tff(c_90, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.32/3.27  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.32/3.27  tff(c_99, plain, (![A_46, B_47]: (r1_tarski(k3_xboole_0(A_46, B_47), A_46))), inference(superposition, [status(thm), theory('equality')], [c_90, c_6])).
% 8.32/3.27  tff(c_18, plain, (![C_21, A_19, B_20]: (r1_tarski(k9_relat_1(C_21, A_19), k9_relat_1(C_21, B_20)) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.32/3.27  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.32/3.27  tff(c_22, plain, (![A_27, B_28]: (v1_funct_1(k7_relat_1(A_27, B_28)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.32/3.27  tff(c_16, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.32/3.27  tff(c_204, plain, (![A_64, C_65, B_66]: (k3_xboole_0(A_64, k10_relat_1(C_65, B_66))=k10_relat_1(k7_relat_1(C_65, A_64), B_66) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.32/3.27  tff(c_222, plain, (![C_65, A_64, B_66]: (r1_tarski(k10_relat_1(k7_relat_1(C_65, A_64), B_66), A_64) | ~v1_relat_1(C_65))), inference(superposition, [status(thm), theory('equality')], [c_204, c_99])).
% 8.32/3.27  tff(c_296, plain, (![A_79, C_80, B_81]: (k9_relat_1(k7_relat_1(A_79, C_80), B_81)=k9_relat_1(A_79, B_81) | ~r1_tarski(B_81, C_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.32/3.27  tff(c_28, plain, (![B_33, A_32]: (r1_tarski(k9_relat_1(B_33, k10_relat_1(B_33, A_32)), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.32/3.27  tff(c_1423, plain, (![A_138, C_139, A_140]: (r1_tarski(k9_relat_1(A_138, k10_relat_1(k7_relat_1(A_138, C_139), A_140)), A_140) | ~v1_funct_1(k7_relat_1(A_138, C_139)) | ~v1_relat_1(k7_relat_1(A_138, C_139)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_138, C_139), A_140), C_139) | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_296, c_28])).
% 8.32/3.27  tff(c_6082, plain, (![C_237, A_238, B_239]: (r1_tarski(k9_relat_1(C_237, k10_relat_1(k7_relat_1(C_237, A_238), B_239)), B_239) | ~v1_funct_1(k7_relat_1(C_237, A_238)) | ~v1_relat_1(k7_relat_1(C_237, A_238)) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_222, c_1423])).
% 8.32/3.27  tff(c_26, plain, (![A_29, C_31, B_30]: (k3_xboole_0(A_29, k10_relat_1(C_31, B_30))=k10_relat_1(k7_relat_1(C_31, A_29), B_30) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.32/3.27  tff(c_193, plain, (![A_61, B_62, C_63]: (r1_tarski(A_61, k3_xboole_0(B_62, C_63)) | ~r1_tarski(A_61, C_63) | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.32/3.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.32/3.27  tff(c_30, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.32/3.27  tff(c_35, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 8.32/3.27  tff(c_203, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_193, c_35])).
% 8.32/3.27  tff(c_315, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_203])).
% 8.32/3.27  tff(c_318, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_315])).
% 8.32/3.27  tff(c_320, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_318])).
% 8.32/3.27  tff(c_6085, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6082, c_320])).
% 8.32/3.27  tff(c_6098, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6085])).
% 8.32/3.27  tff(c_6099, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6098])).
% 8.32/3.27  tff(c_6102, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_6099])).
% 8.32/3.27  tff(c_6106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6102])).
% 8.32/3.27  tff(c_6107, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_6098])).
% 8.32/3.27  tff(c_6111, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_6107])).
% 8.32/3.27  tff(c_6115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_6111])).
% 8.32/3.27  tff(c_6116, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_203])).
% 8.32/3.27  tff(c_6125, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_6116])).
% 8.32/3.27  tff(c_6132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_99, c_6125])).
% 8.32/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.32/3.27  
% 8.32/3.27  Inference rules
% 8.32/3.27  ----------------------
% 8.32/3.27  #Ref     : 0
% 8.32/3.27  #Sup     : 1585
% 8.32/3.27  #Fact    : 0
% 8.32/3.27  #Define  : 0
% 8.32/3.27  #Split   : 2
% 8.32/3.27  #Chain   : 0
% 8.32/3.27  #Close   : 0
% 8.32/3.27  
% 8.32/3.27  Ordering : KBO
% 8.32/3.27  
% 8.32/3.27  Simplification rules
% 8.32/3.27  ----------------------
% 8.32/3.27  #Subsume      : 102
% 8.32/3.27  #Demod        : 1205
% 8.32/3.27  #Tautology    : 459
% 8.32/3.27  #SimpNegUnit  : 0
% 8.32/3.27  #BackRed      : 0
% 8.32/3.27  
% 8.32/3.27  #Partial instantiations: 0
% 8.32/3.27  #Strategies tried      : 1
% 8.32/3.27  
% 8.32/3.27  Timing (in seconds)
% 8.32/3.27  ----------------------
% 8.32/3.27  Preprocessing        : 0.50
% 8.32/3.27  Parsing              : 0.26
% 8.32/3.27  CNF conversion       : 0.03
% 8.32/3.28  Main loop            : 1.86
% 8.32/3.28  Inferencing          : 0.48
% 8.32/3.28  Reduction            : 0.97
% 8.32/3.28  Demodulation         : 0.86
% 8.32/3.28  BG Simplification    : 0.07
% 8.32/3.28  Subsumption          : 0.26
% 8.32/3.28  Abstraction          : 0.10
% 8.32/3.28  MUC search           : 0.00
% 8.32/3.28  Cooper               : 0.00
% 8.32/3.28  Total                : 2.40
% 8.32/3.28  Index Insertion      : 0.00
% 8.32/3.28  Index Deletion       : 0.00
% 8.32/3.28  Index Matching       : 0.00
% 8.32/3.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
