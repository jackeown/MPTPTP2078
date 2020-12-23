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
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   60 (  92 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 124 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [B_35,A_36] : k1_setfam_1(k2_tarski(B_35,A_36)) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_24,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_243,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,k3_xboole_0(k1_relat_1(B_52),A_53)) = k7_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_208,plain,(
    ! [B_46,A_47] :
      ( k5_relat_1(B_46,k6_relat_1(A_47)) = B_46
      | ~ r1_tarski(k2_relat_1(B_46),A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_211,plain,(
    ! [A_17,A_47] :
      ( k5_relat_1(k6_relat_1(A_17),k6_relat_1(A_47)) = k6_relat_1(A_17)
      | ~ r1_tarski(A_17,A_47)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_208])).

tff(c_214,plain,(
    ! [A_48,A_49] :
      ( k5_relat_1(k6_relat_1(A_48),k6_relat_1(A_49)) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_211])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_220,plain,(
    ! [A_49,A_48] :
      ( k7_relat_1(k6_relat_1(A_49),A_48) = k6_relat_1(A_48)
      | ~ v1_relat_1(k6_relat_1(A_49))
      | ~ r1_tarski(A_48,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_22])).

tff(c_230,plain,(
    ! [A_49,A_48] :
      ( k7_relat_1(k6_relat_1(A_49),A_48) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_220])).

tff(c_250,plain,(
    ! [A_49,A_53] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_49)),A_53)) = k7_relat_1(k6_relat_1(A_49),A_53)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_49)),A_53),A_49)
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_230])).

tff(c_271,plain,(
    ! [A_49,A_53] : k7_relat_1(k6_relat_1(A_49),A_53) = k6_relat_1(k3_xboole_0(A_49,A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_16,c_16,c_250])).

tff(c_342,plain,(
    ! [A_58,B_59] :
      ( k10_relat_1(A_58,k1_relat_1(B_59)) = k1_relat_1(k5_relat_1(A_58,B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_351,plain,(
    ! [A_58,A_17] :
      ( k1_relat_1(k5_relat_1(A_58,k6_relat_1(A_17))) = k10_relat_1(A_58,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_342])).

tff(c_889,plain,(
    ! [A_78,A_79] :
      ( k1_relat_1(k5_relat_1(A_78,k6_relat_1(A_79))) = k10_relat_1(A_78,A_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_351])).

tff(c_917,plain,(
    ! [A_79,A_20] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_79),A_20)) = k10_relat_1(k6_relat_1(A_20),A_79)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_889])).

tff(c_924,plain,(
    ! [A_80,A_81] : k10_relat_1(k6_relat_1(A_80),A_81) = k3_xboole_0(A_81,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_16,c_271,c_917])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( k10_relat_1(A_12,k1_relat_1(B_14)) = k1_relat_1(k5_relat_1(A_12,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_931,plain,(
    ! [A_80,B_14] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_80),B_14)) = k3_xboole_0(k1_relat_1(B_14),A_80)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k6_relat_1(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_12])).

tff(c_5612,plain,(
    ! [A_166,B_167] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_166),B_167)) = k3_xboole_0(k1_relat_1(B_167),A_166)
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_931])).

tff(c_28,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_28])).

tff(c_5651,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5612,c_134])).

tff(c_5699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_117,c_5651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:44:09 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.13  
% 5.97/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.13  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.97/2.13  
% 5.97/2.13  %Foreground sorts:
% 5.97/2.13  
% 5.97/2.13  
% 5.97/2.13  %Background operators:
% 5.97/2.13  
% 5.97/2.13  
% 5.97/2.13  %Foreground operators:
% 5.97/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.97/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.97/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.97/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.97/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.97/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.97/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.97/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.97/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.97/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.97/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.97/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.97/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.97/2.13  
% 5.97/2.14  tff(f_71, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 5.97/2.14  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.97/2.14  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.97/2.14  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.97/2.14  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.97/2.14  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.97/2.14  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 5.97/2.14  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 5.97/2.14  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.97/2.14  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.97/2.14  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.97/2.14  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.97/2.14  tff(c_96, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.97/2.14  tff(c_111, plain, (![B_35, A_36]: (k1_setfam_1(k2_tarski(B_35, A_36))=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_4, c_96])).
% 5.97/2.14  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.97/2.14  tff(c_117, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_111, c_10])).
% 5.97/2.14  tff(c_24, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.97/2.14  tff(c_16, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.14  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.97/2.14  tff(c_243, plain, (![B_52, A_53]: (k7_relat_1(B_52, k3_xboole_0(k1_relat_1(B_52), A_53))=k7_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.97/2.14  tff(c_18, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.14  tff(c_208, plain, (![B_46, A_47]: (k5_relat_1(B_46, k6_relat_1(A_47))=B_46 | ~r1_tarski(k2_relat_1(B_46), A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.97/2.14  tff(c_211, plain, (![A_17, A_47]: (k5_relat_1(k6_relat_1(A_17), k6_relat_1(A_47))=k6_relat_1(A_17) | ~r1_tarski(A_17, A_47) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_208])).
% 5.97/2.14  tff(c_214, plain, (![A_48, A_49]: (k5_relat_1(k6_relat_1(A_48), k6_relat_1(A_49))=k6_relat_1(A_48) | ~r1_tarski(A_48, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_211])).
% 5.97/2.14  tff(c_22, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.97/2.14  tff(c_220, plain, (![A_49, A_48]: (k7_relat_1(k6_relat_1(A_49), A_48)=k6_relat_1(A_48) | ~v1_relat_1(k6_relat_1(A_49)) | ~r1_tarski(A_48, A_49))), inference(superposition, [status(thm), theory('equality')], [c_214, c_22])).
% 5.97/2.14  tff(c_230, plain, (![A_49, A_48]: (k7_relat_1(k6_relat_1(A_49), A_48)=k6_relat_1(A_48) | ~r1_tarski(A_48, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_220])).
% 5.97/2.14  tff(c_250, plain, (![A_49, A_53]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_49)), A_53))=k7_relat_1(k6_relat_1(A_49), A_53) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_49)), A_53), A_49) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_230])).
% 5.97/2.14  tff(c_271, plain, (![A_49, A_53]: (k7_relat_1(k6_relat_1(A_49), A_53)=k6_relat_1(k3_xboole_0(A_49, A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_16, c_16, c_250])).
% 5.97/2.14  tff(c_342, plain, (![A_58, B_59]: (k10_relat_1(A_58, k1_relat_1(B_59))=k1_relat_1(k5_relat_1(A_58, B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.14  tff(c_351, plain, (![A_58, A_17]: (k1_relat_1(k5_relat_1(A_58, k6_relat_1(A_17)))=k10_relat_1(A_58, A_17) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_16, c_342])).
% 5.97/2.14  tff(c_889, plain, (![A_78, A_79]: (k1_relat_1(k5_relat_1(A_78, k6_relat_1(A_79)))=k10_relat_1(A_78, A_79) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_351])).
% 5.97/2.14  tff(c_917, plain, (![A_79, A_20]: (k1_relat_1(k7_relat_1(k6_relat_1(A_79), A_20))=k10_relat_1(k6_relat_1(A_20), A_79) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_889])).
% 5.97/2.14  tff(c_924, plain, (![A_80, A_81]: (k10_relat_1(k6_relat_1(A_80), A_81)=k3_xboole_0(A_81, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_16, c_271, c_917])).
% 5.97/2.14  tff(c_12, plain, (![A_12, B_14]: (k10_relat_1(A_12, k1_relat_1(B_14))=k1_relat_1(k5_relat_1(A_12, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.14  tff(c_931, plain, (![A_80, B_14]: (k1_relat_1(k5_relat_1(k6_relat_1(A_80), B_14))=k3_xboole_0(k1_relat_1(B_14), A_80) | ~v1_relat_1(B_14) | ~v1_relat_1(k6_relat_1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_924, c_12])).
% 5.97/2.14  tff(c_5612, plain, (![A_166, B_167]: (k1_relat_1(k5_relat_1(k6_relat_1(A_166), B_167))=k3_xboole_0(k1_relat_1(B_167), A_166) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_931])).
% 5.97/2.14  tff(c_28, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.97/2.14  tff(c_134, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_28])).
% 5.97/2.14  tff(c_5651, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5612, c_134])).
% 5.97/2.14  tff(c_5699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_117, c_5651])).
% 5.97/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.14  
% 5.97/2.14  Inference rules
% 5.97/2.14  ----------------------
% 5.97/2.14  #Ref     : 0
% 5.97/2.14  #Sup     : 1398
% 5.97/2.14  #Fact    : 0
% 5.97/2.14  #Define  : 0
% 5.97/2.15  #Split   : 0
% 5.97/2.15  #Chain   : 0
% 5.97/2.15  #Close   : 0
% 5.97/2.15  
% 5.97/2.15  Ordering : KBO
% 5.97/2.15  
% 5.97/2.15  Simplification rules
% 5.97/2.15  ----------------------
% 5.97/2.15  #Subsume      : 249
% 5.97/2.15  #Demod        : 1480
% 5.97/2.15  #Tautology    : 697
% 5.97/2.15  #SimpNegUnit  : 0
% 5.97/2.15  #BackRed      : 2
% 5.97/2.15  
% 5.97/2.15  #Partial instantiations: 0
% 5.97/2.15  #Strategies tried      : 1
% 5.97/2.15  
% 5.97/2.15  Timing (in seconds)
% 5.97/2.15  ----------------------
% 5.97/2.15  Preprocessing        : 0.29
% 5.97/2.15  Parsing              : 0.16
% 5.97/2.15  CNF conversion       : 0.02
% 5.97/2.15  Main loop            : 1.12
% 5.97/2.15  Inferencing          : 0.33
% 5.97/2.15  Reduction            : 0.55
% 5.97/2.15  Demodulation         : 0.48
% 5.97/2.15  BG Simplification    : 0.04
% 5.97/2.15  Subsumption          : 0.15
% 5.97/2.15  Abstraction          : 0.07
% 5.97/2.15  MUC search           : 0.00
% 5.97/2.15  Cooper               : 0.00
% 5.97/2.15  Total                : 1.43
% 5.97/2.15  Index Insertion      : 0.00
% 5.97/2.15  Index Deletion       : 0.00
% 5.97/2.15  Index Matching       : 0.00
% 5.97/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
