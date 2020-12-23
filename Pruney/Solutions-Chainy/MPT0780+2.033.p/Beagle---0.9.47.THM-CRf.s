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
% DateTime   : Thu Dec  3 10:06:43 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   61 (  76 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  94 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_35] : k2_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [B_40,A_39] : k5_relat_1(k6_relat_1(B_40),k6_relat_1(A_39)) = k6_relat_1(k3_xboole_0(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_260,plain,(
    ! [B_78,A_79] :
      ( k9_relat_1(B_78,k2_relat_1(A_79)) = k2_relat_1(k5_relat_1(A_79,B_78))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_280,plain,(
    ! [A_35,B_78] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_35),B_78)) = k9_relat_1(B_78,A_35)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_260])).

tff(c_289,plain,(
    ! [A_80,B_81] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_80),B_81)) = k9_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_280])).

tff(c_301,plain,(
    ! [A_39,B_40] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_39,B_40))) = k9_relat_1(k6_relat_1(A_39),B_40)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_289])).

tff(c_305,plain,(
    ! [A_39,B_40] : k9_relat_1(k6_relat_1(A_39),B_40) = k3_xboole_0(A_39,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_301])).

tff(c_20,plain,(
    ! [A_35] : k1_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106,plain,(
    ! [B_62,A_63] :
      ( k7_relat_1(B_62,A_63) = B_62
      | ~ r1_tarski(k1_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [A_35,A_63] :
      ( k7_relat_1(k6_relat_1(A_35),A_63) = k6_relat_1(A_35)
      | ~ r1_tarski(A_35,A_63)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_106])).

tff(c_112,plain,(
    ! [A_64,A_65] :
      ( k7_relat_1(k6_relat_1(A_64),A_65) = k6_relat_1(A_64)
      | ~ r1_tarski(A_64,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_16,plain,(
    ! [B_31,A_30] :
      ( k2_relat_1(k7_relat_1(B_31,A_30)) = k9_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_64,A_65] :
      ( k9_relat_1(k6_relat_1(A_64),A_65) = k2_relat_1(k6_relat_1(A_64))
      | ~ v1_relat_1(k6_relat_1(A_64))
      | ~ r1_tarski(A_64,A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_124,plain,(
    ! [A_64,A_65] :
      ( k9_relat_1(k6_relat_1(A_64),A_65) = A_64
      | ~ r1_tarski(A_64,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_118])).

tff(c_337,plain,(
    ! [A_89,A_90] :
      ( k3_xboole_0(A_89,A_90) = A_89
      | ~ r1_tarski(A_89,A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_124])).

tff(c_341,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_337])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [C_43,A_41,B_42] :
      ( k2_wellord1(k2_wellord1(C_43,A_41),B_42) = k2_wellord1(C_43,k3_xboole_0(A_41,B_42))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_164,plain,(
    ! [C_75,B_76,A_77] :
      ( k2_wellord1(k2_wellord1(C_75,B_76),A_77) = k2_wellord1(k2_wellord1(C_75,A_77),B_76)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_36])).

tff(c_248,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_203])).

tff(c_257,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_248])).

tff(c_259,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_257])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.33  
% 2.29/1.33  %Foreground sorts:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Background operators:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Foreground operators:
% 2.29/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.29/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.29/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.29/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.29/1.33  
% 2.29/1.35  tff(f_81, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 2.29/1.35  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.29/1.35  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.29/1.35  tff(f_66, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.29/1.35  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.29/1.35  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.29/1.35  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.29/1.35  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 2.29/1.35  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 2.29/1.35  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.35  tff(c_26, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.35  tff(c_22, plain, (![A_35]: (k2_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.29/1.35  tff(c_30, plain, (![B_40, A_39]: (k5_relat_1(k6_relat_1(B_40), k6_relat_1(A_39))=k6_relat_1(k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.35  tff(c_260, plain, (![B_78, A_79]: (k9_relat_1(B_78, k2_relat_1(A_79))=k2_relat_1(k5_relat_1(A_79, B_78)) | ~v1_relat_1(B_78) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.35  tff(c_280, plain, (![A_35, B_78]: (k2_relat_1(k5_relat_1(k6_relat_1(A_35), B_78))=k9_relat_1(B_78, A_35) | ~v1_relat_1(B_78) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_260])).
% 2.29/1.35  tff(c_289, plain, (![A_80, B_81]: (k2_relat_1(k5_relat_1(k6_relat_1(A_80), B_81))=k9_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_280])).
% 2.29/1.35  tff(c_301, plain, (![A_39, B_40]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_39, B_40)))=k9_relat_1(k6_relat_1(A_39), B_40) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_289])).
% 2.29/1.35  tff(c_305, plain, (![A_39, B_40]: (k9_relat_1(k6_relat_1(A_39), B_40)=k3_xboole_0(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_301])).
% 2.29/1.35  tff(c_20, plain, (![A_35]: (k1_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.29/1.35  tff(c_106, plain, (![B_62, A_63]: (k7_relat_1(B_62, A_63)=B_62 | ~r1_tarski(k1_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.35  tff(c_109, plain, (![A_35, A_63]: (k7_relat_1(k6_relat_1(A_35), A_63)=k6_relat_1(A_35) | ~r1_tarski(A_35, A_63) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_106])).
% 2.29/1.35  tff(c_112, plain, (![A_64, A_65]: (k7_relat_1(k6_relat_1(A_64), A_65)=k6_relat_1(A_64) | ~r1_tarski(A_64, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_109])).
% 2.29/1.35  tff(c_16, plain, (![B_31, A_30]: (k2_relat_1(k7_relat_1(B_31, A_30))=k9_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.35  tff(c_118, plain, (![A_64, A_65]: (k9_relat_1(k6_relat_1(A_64), A_65)=k2_relat_1(k6_relat_1(A_64)) | ~v1_relat_1(k6_relat_1(A_64)) | ~r1_tarski(A_64, A_65))), inference(superposition, [status(thm), theory('equality')], [c_112, c_16])).
% 2.29/1.35  tff(c_124, plain, (![A_64, A_65]: (k9_relat_1(k6_relat_1(A_64), A_65)=A_64 | ~r1_tarski(A_64, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_118])).
% 2.29/1.35  tff(c_337, plain, (![A_89, A_90]: (k3_xboole_0(A_89, A_90)=A_89 | ~r1_tarski(A_89, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_124])).
% 2.29/1.35  tff(c_341, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_337])).
% 2.29/1.35  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.35  tff(c_32, plain, (![C_43, A_41, B_42]: (k2_wellord1(k2_wellord1(C_43, A_41), B_42)=k2_wellord1(C_43, k3_xboole_0(A_41, B_42)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.29/1.35  tff(c_164, plain, (![C_75, B_76, A_77]: (k2_wellord1(k2_wellord1(C_75, B_76), A_77)=k2_wellord1(k2_wellord1(C_75, A_77), B_76) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.29/1.35  tff(c_36, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.35  tff(c_203, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_164, c_36])).
% 2.29/1.35  tff(c_248, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_203])).
% 2.29/1.35  tff(c_257, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_248])).
% 2.29/1.35  tff(c_259, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_257])).
% 2.29/1.35  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_259])).
% 2.29/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.35  
% 2.29/1.35  Inference rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Ref     : 0
% 2.29/1.35  #Sup     : 71
% 2.29/1.35  #Fact    : 0
% 2.29/1.35  #Define  : 0
% 2.29/1.35  #Split   : 0
% 2.29/1.35  #Chain   : 0
% 2.29/1.35  #Close   : 0
% 2.29/1.35  
% 2.29/1.35  Ordering : KBO
% 2.29/1.35  
% 2.29/1.35  Simplification rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Subsume      : 1
% 2.29/1.35  #Demod        : 16
% 2.29/1.35  #Tautology    : 38
% 2.29/1.35  #SimpNegUnit  : 0
% 2.29/1.35  #BackRed      : 2
% 2.29/1.35  
% 2.29/1.35  #Partial instantiations: 0
% 2.29/1.35  #Strategies tried      : 1
% 2.29/1.35  
% 2.29/1.35  Timing (in seconds)
% 2.29/1.35  ----------------------
% 2.29/1.35  Preprocessing        : 0.35
% 2.29/1.35  Parsing              : 0.19
% 2.29/1.35  CNF conversion       : 0.02
% 2.29/1.35  Main loop            : 0.22
% 2.29/1.35  Inferencing          : 0.09
% 2.29/1.35  Reduction            : 0.06
% 2.29/1.35  Demodulation         : 0.05
% 2.29/1.35  BG Simplification    : 0.02
% 2.29/1.35  Subsumption          : 0.03
% 2.29/1.35  Abstraction          : 0.02
% 2.29/1.35  MUC search           : 0.00
% 2.29/1.35  Cooper               : 0.00
% 2.29/1.35  Total                : 0.60
% 2.29/1.35  Index Insertion      : 0.00
% 2.29/1.35  Index Deletion       : 0.00
% 2.29/1.35  Index Matching       : 0.00
% 2.29/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
