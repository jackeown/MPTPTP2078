%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:53 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 131 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 218 expanded)
%              Number of equality atoms :   12 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_79,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5809,plain,(
    ! [C_238,A_239,D_240,B_241] :
      ( r1_tarski(k9_relat_1(C_238,A_239),k9_relat_1(D_240,B_241))
      | ~ r1_tarski(A_239,B_241)
      | ~ r1_tarski(C_238,D_240)
      | ~ v1_relat_1(D_240)
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    ! [A_33,B_34] :
      ( v1_funct_1(k7_relat_1(A_33,B_34))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_774,plain,(
    ! [A_96,C_97,B_98] :
      ( k3_xboole_0(A_96,k10_relat_1(C_97,B_98)) = k10_relat_1(k7_relat_1(C_97,A_96),B_98)
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_844,plain,(
    ! [C_97,A_96,B_98] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_97,A_96),B_98),A_96)
      | ~ v1_relat_1(C_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_8])).

tff(c_1290,plain,(
    ! [A_105,C_106,B_107] :
      ( k9_relat_1(k7_relat_1(A_105,C_106),B_107) = k9_relat_1(A_105,B_107)
      | ~ r1_tarski(B_107,C_106)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [B_39,A_38] :
      ( r1_tarski(k9_relat_1(B_39,k10_relat_1(B_39,A_38)),A_38)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2880,plain,(
    ! [A_147,C_148,A_149] :
      ( r1_tarski(k9_relat_1(A_147,k10_relat_1(k7_relat_1(A_147,C_148),A_149)),A_149)
      | ~ v1_funct_1(k7_relat_1(A_147,C_148))
      | ~ v1_relat_1(k7_relat_1(A_147,C_148))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_147,C_148),A_149),C_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_34])).

tff(c_4751,plain,(
    ! [C_209,A_210,B_211] :
      ( r1_tarski(k9_relat_1(C_209,k10_relat_1(k7_relat_1(C_209,A_210),B_211)),B_211)
      | ~ v1_funct_1(k7_relat_1(C_209,A_210))
      | ~ v1_relat_1(k7_relat_1(C_209,A_210))
      | ~ v1_relat_1(C_209) ) ),
    inference(resolution,[status(thm)],[c_844,c_2880])).

tff(c_236,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(A_76,k3_xboole_0(B_77,C_78))
      | ~ r1_tarski(A_76,C_78)
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [B_51,A_52] : k1_setfam_1(k2_tarski(B_51,A_52)) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_20,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_20])).

tff(c_36,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_125,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_36])).

tff(c_273,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_236,c_125])).

tff(c_335,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_793,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_335])).

tff(c_875,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_793])).

tff(c_4771,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4751,c_875])).

tff(c_4794,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4771])).

tff(c_4799,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4794])).

tff(c_4802,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_4799])).

tff(c_4806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4802])).

tff(c_4807,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4794])).

tff(c_4811,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_4807])).

tff(c_4815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4811])).

tff(c_4816,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_5812,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5809,c_4816])).

tff(c_5830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_8,c_5812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.03  
% 5.50/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.03  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.50/2.03  
% 5.50/2.03  %Foreground sorts:
% 5.50/2.03  
% 5.50/2.03  
% 5.50/2.03  %Background operators:
% 5.50/2.03  
% 5.50/2.03  
% 5.50/2.03  %Foreground operators:
% 5.50/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.50/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.03  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.50/2.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.50/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.50/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.50/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.50/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.03  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.50/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.50/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.03  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.50/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.50/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.50/2.03  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.50/2.03  
% 5.50/2.04  tff(f_96, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 5.50/2.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.50/2.04  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.50/2.04  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 5.50/2.04  tff(f_79, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 5.50/2.04  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.50/2.04  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.50/2.04  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 5.50/2.04  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 5.50/2.04  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.50/2.04  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.50/2.04  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.50/2.04  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.50/2.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.50/2.04  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.50/2.04  tff(c_5809, plain, (![C_238, A_239, D_240, B_241]: (r1_tarski(k9_relat_1(C_238, A_239), k9_relat_1(D_240, B_241)) | ~r1_tarski(A_239, B_241) | ~r1_tarski(C_238, D_240) | ~v1_relat_1(D_240) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.50/2.04  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.50/2.04  tff(c_28, plain, (![A_33, B_34]: (v1_funct_1(k7_relat_1(A_33, B_34)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.50/2.04  tff(c_22, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.50/2.04  tff(c_774, plain, (![A_96, C_97, B_98]: (k3_xboole_0(A_96, k10_relat_1(C_97, B_98))=k10_relat_1(k7_relat_1(C_97, A_96), B_98) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.50/2.04  tff(c_844, plain, (![C_97, A_96, B_98]: (r1_tarski(k10_relat_1(k7_relat_1(C_97, A_96), B_98), A_96) | ~v1_relat_1(C_97))), inference(superposition, [status(thm), theory('equality')], [c_774, c_8])).
% 5.50/2.04  tff(c_1290, plain, (![A_105, C_106, B_107]: (k9_relat_1(k7_relat_1(A_105, C_106), B_107)=k9_relat_1(A_105, B_107) | ~r1_tarski(B_107, C_106) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.50/2.04  tff(c_34, plain, (![B_39, A_38]: (r1_tarski(k9_relat_1(B_39, k10_relat_1(B_39, A_38)), A_38) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.50/2.04  tff(c_2880, plain, (![A_147, C_148, A_149]: (r1_tarski(k9_relat_1(A_147, k10_relat_1(k7_relat_1(A_147, C_148), A_149)), A_149) | ~v1_funct_1(k7_relat_1(A_147, C_148)) | ~v1_relat_1(k7_relat_1(A_147, C_148)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_147, C_148), A_149), C_148) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_1290, c_34])).
% 5.50/2.04  tff(c_4751, plain, (![C_209, A_210, B_211]: (r1_tarski(k9_relat_1(C_209, k10_relat_1(k7_relat_1(C_209, A_210), B_211)), B_211) | ~v1_funct_1(k7_relat_1(C_209, A_210)) | ~v1_relat_1(k7_relat_1(C_209, A_210)) | ~v1_relat_1(C_209))), inference(resolution, [status(thm)], [c_844, c_2880])).
% 5.50/2.04  tff(c_236, plain, (![A_76, B_77, C_78]: (r1_tarski(A_76, k3_xboole_0(B_77, C_78)) | ~r1_tarski(A_76, C_78) | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.50/2.04  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.50/2.04  tff(c_87, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.04  tff(c_102, plain, (![B_51, A_52]: (k1_setfam_1(k2_tarski(B_51, A_52))=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_12, c_87])).
% 5.50/2.04  tff(c_20, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.04  tff(c_108, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_102, c_20])).
% 5.50/2.04  tff(c_36, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.50/2.04  tff(c_125, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_36])).
% 5.50/2.04  tff(c_273, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_236, c_125])).
% 5.50/2.04  tff(c_335, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_273])).
% 5.50/2.04  tff(c_793, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_774, c_335])).
% 5.50/2.04  tff(c_875, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_793])).
% 5.50/2.04  tff(c_4771, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4751, c_875])).
% 5.50/2.04  tff(c_4794, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4771])).
% 5.50/2.04  tff(c_4799, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4794])).
% 5.50/2.04  tff(c_4802, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_4799])).
% 5.50/2.04  tff(c_4806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_4802])).
% 5.50/2.04  tff(c_4807, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_4794])).
% 5.50/2.04  tff(c_4811, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_4807])).
% 5.50/2.04  tff(c_4815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4811])).
% 5.50/2.04  tff(c_4816, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_273])).
% 5.50/2.04  tff(c_5812, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5809, c_4816])).
% 5.50/2.04  tff(c_5830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_8, c_5812])).
% 5.50/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.04  
% 5.50/2.04  Inference rules
% 5.50/2.04  ----------------------
% 5.50/2.04  #Ref     : 0
% 5.50/2.04  #Sup     : 1429
% 5.50/2.04  #Fact    : 0
% 5.50/2.04  #Define  : 0
% 5.50/2.04  #Split   : 3
% 5.50/2.04  #Chain   : 0
% 5.50/2.04  #Close   : 0
% 5.50/2.04  
% 5.50/2.04  Ordering : KBO
% 5.50/2.04  
% 5.50/2.04  Simplification rules
% 5.50/2.04  ----------------------
% 5.50/2.04  #Subsume      : 363
% 5.50/2.04  #Demod        : 1432
% 5.50/2.04  #Tautology    : 645
% 5.50/2.04  #SimpNegUnit  : 0
% 5.50/2.04  #BackRed      : 1
% 5.50/2.04  
% 5.50/2.04  #Partial instantiations: 0
% 5.50/2.04  #Strategies tried      : 1
% 5.50/2.04  
% 5.50/2.04  Timing (in seconds)
% 5.50/2.04  ----------------------
% 5.50/2.05  Preprocessing        : 0.30
% 5.50/2.05  Parsing              : 0.16
% 5.50/2.05  CNF conversion       : 0.02
% 5.50/2.05  Main loop            : 1.03
% 5.50/2.05  Inferencing          : 0.29
% 5.50/2.05  Reduction            : 0.46
% 5.50/2.05  Demodulation         : 0.39
% 5.50/2.05  BG Simplification    : 0.04
% 5.50/2.05  Subsumption          : 0.19
% 5.50/2.05  Abstraction          : 0.06
% 5.50/2.05  MUC search           : 0.00
% 5.50/2.05  Cooper               : 0.00
% 5.50/2.05  Total                : 1.36
% 5.50/2.05  Index Insertion      : 0.00
% 5.50/2.05  Index Deletion       : 0.00
% 5.50/2.05  Index Matching       : 0.00
% 5.50/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
