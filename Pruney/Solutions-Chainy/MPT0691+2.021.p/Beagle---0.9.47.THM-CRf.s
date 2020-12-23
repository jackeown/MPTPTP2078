%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 215 expanded)
%              Number of leaves         :   24 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :   81 ( 413 expanded)
%              Number of equality atoms :   28 ( 111 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_167,plain,(
    ! [B_34,A_35] :
      ( k1_relat_1(k7_relat_1(B_34,A_35)) = A_35
      | ~ r1_tarski(A_35,k1_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_178,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_167])).

tff(c_183,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_178])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_187,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_14])).

tff(c_233,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_236,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_233])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_236])).

tff(c_242,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_12,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_191,plain,(
    ! [A_36,C_37,B_38] :
      ( k3_xboole_0(A_36,k10_relat_1(C_37,B_38)) = k10_relat_1(k7_relat_1(C_37,A_36),B_38)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_223,plain,(
    ! [C_39,A_40,B_41] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_39,A_40),B_41),A_40)
      | ~ v1_relat_1(C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_2])).

tff(c_1356,plain,(
    ! [B_89,C_90,B_91] :
      ( k1_relat_1(k7_relat_1(B_89,k10_relat_1(k7_relat_1(C_90,k1_relat_1(B_89)),B_91))) = k10_relat_1(k7_relat_1(C_90,k1_relat_1(B_89)),B_91)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_223,c_14])).

tff(c_1455,plain,(
    ! [C_90,B_91] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(k7_relat_1(C_90,'#skF_1'),B_91))) = k10_relat_1(k7_relat_1(C_90,k1_relat_1(k7_relat_1('#skF_2','#skF_1'))),B_91)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_1356])).

tff(c_1472,plain,(
    ! [C_92,B_93] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(k7_relat_1(C_92,'#skF_1'),B_93))) = k10_relat_1(k7_relat_1(C_92,'#skF_1'),B_93)
      | ~ v1_relat_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_183,c_1455])).

tff(c_1807,plain,(
    ! [C_104] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k1_relat_1(k7_relat_1(C_104,'#skF_1')))) = k10_relat_1(k7_relat_1(C_104,'#skF_1'),k2_relat_1(k7_relat_1(C_104,'#skF_1')))
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(k7_relat_1(C_104,'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1472])).

tff(c_1897,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_1807])).

tff(c_1912,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_22,c_1897])).

tff(c_1971,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1912,c_12])).

tff(c_2007,plain,(
    k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_183,c_1971])).

tff(c_2013,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2007,c_1912])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(B_26,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6])).

tff(c_111,plain,(
    ! [B_27,A_28] : r1_tarski(k3_xboole_0(B_27,A_28),A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_197,plain,(
    ! [C_37,A_36,B_38] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_37,A_36),B_38),k10_relat_1(C_37,B_38))
      | ~ v1_relat_1(C_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_111])).

tff(c_2269,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2013,c_197])).

tff(c_2309,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2269])).

tff(c_2325,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2309])).

tff(c_2327,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2325])).

tff(c_2329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_2327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 12:10:59 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.68  
% 4.09/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.68  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.09/1.68  
% 4.09/1.68  %Foreground sorts:
% 4.09/1.68  
% 4.09/1.68  
% 4.09/1.68  %Background operators:
% 4.09/1.68  
% 4.09/1.68  
% 4.09/1.68  %Foreground operators:
% 4.09/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.09/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.09/1.68  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.09/1.68  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.09/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.09/1.68  
% 4.09/1.69  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.09/1.69  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.09/1.69  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.09/1.69  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.09/1.69  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.09/1.69  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.09/1.69  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.09/1.69  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.09/1.69  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.09/1.69  tff(c_18, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.09/1.69  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.09/1.69  tff(c_10, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.69  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.69  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.09/1.69  tff(c_167, plain, (![B_34, A_35]: (k1_relat_1(k7_relat_1(B_34, A_35))=A_35 | ~r1_tarski(A_35, k1_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.09/1.69  tff(c_178, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_167])).
% 4.09/1.69  tff(c_183, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_178])).
% 4.09/1.69  tff(c_14, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.09/1.69  tff(c_187, plain, (![A_12]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_14])).
% 4.09/1.69  tff(c_233, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_187])).
% 4.09/1.69  tff(c_236, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_233])).
% 4.09/1.69  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_236])).
% 4.09/1.69  tff(c_242, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_187])).
% 4.09/1.69  tff(c_12, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.69  tff(c_191, plain, (![A_36, C_37, B_38]: (k3_xboole_0(A_36, k10_relat_1(C_37, B_38))=k10_relat_1(k7_relat_1(C_37, A_36), B_38) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.09/1.69  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.09/1.69  tff(c_223, plain, (![C_39, A_40, B_41]: (r1_tarski(k10_relat_1(k7_relat_1(C_39, A_40), B_41), A_40) | ~v1_relat_1(C_39))), inference(superposition, [status(thm), theory('equality')], [c_191, c_2])).
% 4.09/1.69  tff(c_1356, plain, (![B_89, C_90, B_91]: (k1_relat_1(k7_relat_1(B_89, k10_relat_1(k7_relat_1(C_90, k1_relat_1(B_89)), B_91)))=k10_relat_1(k7_relat_1(C_90, k1_relat_1(B_89)), B_91) | ~v1_relat_1(B_89) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_223, c_14])).
% 4.09/1.69  tff(c_1455, plain, (![C_90, B_91]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(k7_relat_1(C_90, '#skF_1'), B_91)))=k10_relat_1(k7_relat_1(C_90, k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), B_91) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_183, c_1356])).
% 4.09/1.69  tff(c_1472, plain, (![C_92, B_93]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(k7_relat_1(C_92, '#skF_1'), B_93)))=k10_relat_1(k7_relat_1(C_92, '#skF_1'), B_93) | ~v1_relat_1(C_92))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_183, c_1455])).
% 4.09/1.69  tff(c_1807, plain, (![C_104]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k1_relat_1(k7_relat_1(C_104, '#skF_1'))))=k10_relat_1(k7_relat_1(C_104, '#skF_1'), k2_relat_1(k7_relat_1(C_104, '#skF_1'))) | ~v1_relat_1(C_104) | ~v1_relat_1(k7_relat_1(C_104, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1472])).
% 4.09/1.69  tff(c_1897, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_1807])).
% 4.09/1.69  tff(c_1912, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_22, c_1897])).
% 4.09/1.69  tff(c_1971, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1912, c_12])).
% 4.09/1.69  tff(c_2007, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_183, c_1971])).
% 4.09/1.69  tff(c_2013, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2007, c_1912])).
% 4.09/1.69  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.69  tff(c_58, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.69  tff(c_73, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(B_26, A_25))), inference(superposition, [status(thm), theory('equality')], [c_4, c_58])).
% 4.09/1.69  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.69  tff(c_96, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6])).
% 4.09/1.69  tff(c_111, plain, (![B_27, A_28]: (r1_tarski(k3_xboole_0(B_27, A_28), A_28))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 4.09/1.69  tff(c_197, plain, (![C_37, A_36, B_38]: (r1_tarski(k10_relat_1(k7_relat_1(C_37, A_36), B_38), k10_relat_1(C_37, B_38)) | ~v1_relat_1(C_37))), inference(superposition, [status(thm), theory('equality')], [c_191, c_111])).
% 4.09/1.69  tff(c_2269, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2013, c_197])).
% 4.09/1.69  tff(c_2309, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2269])).
% 4.09/1.69  tff(c_2325, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_2309])).
% 4.09/1.69  tff(c_2327, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2325])).
% 4.09/1.69  tff(c_2329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_2327])).
% 4.09/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.69  
% 4.09/1.69  Inference rules
% 4.09/1.69  ----------------------
% 4.09/1.69  #Ref     : 0
% 4.09/1.69  #Sup     : 570
% 4.09/1.69  #Fact    : 0
% 4.09/1.69  #Define  : 0
% 4.09/1.69  #Split   : 1
% 4.09/1.69  #Chain   : 0
% 4.09/1.69  #Close   : 0
% 4.09/1.69  
% 4.09/1.69  Ordering : KBO
% 4.09/1.69  
% 4.09/1.69  Simplification rules
% 4.09/1.69  ----------------------
% 4.09/1.69  #Subsume      : 78
% 4.09/1.69  #Demod        : 307
% 4.09/1.69  #Tautology    : 163
% 4.09/1.69  #SimpNegUnit  : 1
% 4.09/1.69  #BackRed      : 1
% 4.09/1.69  
% 4.09/1.69  #Partial instantiations: 0
% 4.09/1.69  #Strategies tried      : 1
% 4.09/1.69  
% 4.09/1.69  Timing (in seconds)
% 4.09/1.69  ----------------------
% 4.09/1.70  Preprocessing        : 0.29
% 4.09/1.70  Parsing              : 0.15
% 4.09/1.70  CNF conversion       : 0.02
% 4.09/1.70  Main loop            : 0.68
% 4.09/1.70  Inferencing          : 0.23
% 4.09/1.70  Reduction            : 0.26
% 4.09/1.70  Demodulation         : 0.21
% 4.09/1.70  BG Simplification    : 0.03
% 4.09/1.70  Subsumption          : 0.11
% 4.09/1.70  Abstraction          : 0.04
% 4.09/1.70  MUC search           : 0.00
% 4.09/1.70  Cooper               : 0.00
% 4.09/1.70  Total                : 0.99
% 4.09/1.70  Index Insertion      : 0.00
% 4.09/1.70  Index Deletion       : 0.00
% 4.09/1.70  Index Matching       : 0.00
% 4.09/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
