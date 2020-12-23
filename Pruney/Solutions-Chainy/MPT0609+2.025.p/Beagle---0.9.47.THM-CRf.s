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
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 103 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_37,B_38] : k6_subset_1(A_37,B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [C_43,A_41,B_42] :
      ( k7_relat_1(C_43,k6_subset_1(A_41,B_42)) = k6_subset_1(C_43,k7_relat_1(C_43,B_42))
      | ~ r1_tarski(k1_relat_1(C_43),A_41)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_401,plain,(
    ! [C_104,A_105,B_106] :
      ( k7_relat_1(C_104,k4_xboole_0(A_105,B_106)) = k4_xboole_0(C_104,k7_relat_1(C_104,B_106))
      | ~ r1_tarski(k1_relat_1(C_104),A_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_30])).

tff(c_417,plain,(
    ! [C_107,B_108] :
      ( k7_relat_1(C_107,k4_xboole_0(k1_relat_1(C_107),B_108)) = k4_xboole_0(C_107,k7_relat_1(C_107,B_108))
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_6,c_401])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(k7_relat_1(B_77,A_78)) = A_78
      | ~ r1_tarski(A_78,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_157,plain,(
    ! [B_77,A_5,C_7] :
      ( k1_relat_1(k7_relat_1(B_77,k4_xboole_0(A_5,C_7))) = k4_xboole_0(A_5,C_7)
      | ~ v1_relat_1(B_77)
      | ~ r1_tarski(A_5,k1_relat_1(B_77)) ) ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_423,plain,(
    ! [C_107,B_108] :
      ( k1_relat_1(k4_xboole_0(C_107,k7_relat_1(C_107,B_108))) = k4_xboole_0(k1_relat_1(C_107),B_108)
      | ~ v1_relat_1(C_107)
      | ~ r1_tarski(k1_relat_1(C_107),k1_relat_1(C_107))
      | ~ v1_relat_1(C_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_157])).

tff(c_450,plain,(
    ! [C_107,B_108] :
      ( k1_relat_1(k4_xboole_0(C_107,k7_relat_1(C_107,B_108))) = k4_xboole_0(k1_relat_1(C_107),B_108)
      | ~ v1_relat_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_423])).

tff(c_32,plain,(
    ! [B_45,A_44] :
      ( k3_xboole_0(k1_relat_1(B_45),A_44) = k1_relat_1(k7_relat_1(B_45,A_44))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_238,plain,(
    ! [B_96,B_97] :
      ( k1_relat_1(k7_relat_1(B_96,k3_xboole_0(k1_relat_1(B_96),B_97))) = k3_xboole_0(k1_relat_1(B_96),B_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_109,plain,(
    ! [B_69,A_70] :
      ( k3_xboole_0(k1_relat_1(B_69),A_70) = k1_relat_1(k7_relat_1(B_69,A_70))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_118,plain,(
    ! [B_69,A_70] :
      ( k5_xboole_0(k1_relat_1(B_69),k1_relat_1(k7_relat_1(B_69,A_70))) = k4_xboole_0(k1_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_250,plain,(
    ! [B_96,B_97] :
      ( k5_xboole_0(k1_relat_1(B_96),k3_xboole_0(k1_relat_1(B_96),B_97)) = k4_xboole_0(k1_relat_1(B_96),k3_xboole_0(k1_relat_1(B_96),B_97))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_118])).

tff(c_1021,plain,(
    ! [B_137,B_138] :
      ( k4_xboole_0(k1_relat_1(B_137),k3_xboole_0(k1_relat_1(B_137),B_138)) = k4_xboole_0(k1_relat_1(B_137),B_138)
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_250])).

tff(c_1251,plain,(
    ! [B_150,A_151] :
      ( k4_xboole_0(k1_relat_1(B_150),k1_relat_1(k7_relat_1(B_150,A_151))) = k4_xboole_0(k1_relat_1(B_150),A_151)
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1021])).

tff(c_36,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_36])).

tff(c_1283,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_39])).

tff(c_1334,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_38,c_1283])).

tff(c_1343,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_1334])).

tff(c_1347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.52  
% 3.35/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.52  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.35/1.52  
% 3.35/1.52  %Foreground sorts:
% 3.35/1.52  
% 3.35/1.52  
% 3.35/1.52  %Background operators:
% 3.35/1.52  
% 3.35/1.52  
% 3.35/1.52  %Foreground operators:
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.35/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.52  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.35/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.35/1.52  
% 3.47/1.54  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 3.47/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.54  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.47/1.54  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 3.47/1.54  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.47/1.54  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.47/1.54  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.47/1.54  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.47/1.54  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.47/1.54  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.47/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.54  tff(c_26, plain, (![A_37, B_38]: (k6_subset_1(A_37, B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.47/1.54  tff(c_30, plain, (![C_43, A_41, B_42]: (k7_relat_1(C_43, k6_subset_1(A_41, B_42))=k6_subset_1(C_43, k7_relat_1(C_43, B_42)) | ~r1_tarski(k1_relat_1(C_43), A_41) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.54  tff(c_401, plain, (![C_104, A_105, B_106]: (k7_relat_1(C_104, k4_xboole_0(A_105, B_106))=k4_xboole_0(C_104, k7_relat_1(C_104, B_106)) | ~r1_tarski(k1_relat_1(C_104), A_105) | ~v1_relat_1(C_104))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_30])).
% 3.47/1.54  tff(c_417, plain, (![C_107, B_108]: (k7_relat_1(C_107, k4_xboole_0(k1_relat_1(C_107), B_108))=k4_xboole_0(C_107, k7_relat_1(C_107, B_108)) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_6, c_401])).
% 3.47/1.54  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.47/1.54  tff(c_140, plain, (![B_77, A_78]: (k1_relat_1(k7_relat_1(B_77, A_78))=A_78 | ~r1_tarski(A_78, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.54  tff(c_157, plain, (![B_77, A_5, C_7]: (k1_relat_1(k7_relat_1(B_77, k4_xboole_0(A_5, C_7)))=k4_xboole_0(A_5, C_7) | ~v1_relat_1(B_77) | ~r1_tarski(A_5, k1_relat_1(B_77)))), inference(resolution, [status(thm)], [c_10, c_140])).
% 3.47/1.54  tff(c_423, plain, (![C_107, B_108]: (k1_relat_1(k4_xboole_0(C_107, k7_relat_1(C_107, B_108)))=k4_xboole_0(k1_relat_1(C_107), B_108) | ~v1_relat_1(C_107) | ~r1_tarski(k1_relat_1(C_107), k1_relat_1(C_107)) | ~v1_relat_1(C_107))), inference(superposition, [status(thm), theory('equality')], [c_417, c_157])).
% 3.47/1.54  tff(c_450, plain, (![C_107, B_108]: (k1_relat_1(k4_xboole_0(C_107, k7_relat_1(C_107, B_108)))=k4_xboole_0(k1_relat_1(C_107), B_108) | ~v1_relat_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_423])).
% 3.47/1.54  tff(c_32, plain, (![B_45, A_44]: (k3_xboole_0(k1_relat_1(B_45), A_44)=k1_relat_1(k7_relat_1(B_45, A_44)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.54  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.47/1.54  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.54  tff(c_238, plain, (![B_96, B_97]: (k1_relat_1(k7_relat_1(B_96, k3_xboole_0(k1_relat_1(B_96), B_97)))=k3_xboole_0(k1_relat_1(B_96), B_97) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_12, c_140])).
% 3.47/1.54  tff(c_109, plain, (![B_69, A_70]: (k3_xboole_0(k1_relat_1(B_69), A_70)=k1_relat_1(k7_relat_1(B_69, A_70)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.54  tff(c_118, plain, (![B_69, A_70]: (k5_xboole_0(k1_relat_1(B_69), k1_relat_1(k7_relat_1(B_69, A_70)))=k4_xboole_0(k1_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 3.47/1.54  tff(c_250, plain, (![B_96, B_97]: (k5_xboole_0(k1_relat_1(B_96), k3_xboole_0(k1_relat_1(B_96), B_97))=k4_xboole_0(k1_relat_1(B_96), k3_xboole_0(k1_relat_1(B_96), B_97)) | ~v1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_238, c_118])).
% 3.47/1.54  tff(c_1021, plain, (![B_137, B_138]: (k4_xboole_0(k1_relat_1(B_137), k3_xboole_0(k1_relat_1(B_137), B_138))=k4_xboole_0(k1_relat_1(B_137), B_138) | ~v1_relat_1(B_137) | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_250])).
% 3.47/1.54  tff(c_1251, plain, (![B_150, A_151]: (k4_xboole_0(k1_relat_1(B_150), k1_relat_1(k7_relat_1(B_150, A_151)))=k4_xboole_0(k1_relat_1(B_150), A_151) | ~v1_relat_1(B_150) | ~v1_relat_1(B_150) | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1021])).
% 3.47/1.54  tff(c_36, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.47/1.54  tff(c_39, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_36])).
% 3.47/1.54  tff(c_1283, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1251, c_39])).
% 3.47/1.54  tff(c_1334, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_38, c_1283])).
% 3.47/1.54  tff(c_1343, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_450, c_1334])).
% 3.47/1.54  tff(c_1347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1343])).
% 3.47/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.54  
% 3.47/1.54  Inference rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Ref     : 0
% 3.47/1.54  #Sup     : 382
% 3.47/1.54  #Fact    : 0
% 3.47/1.54  #Define  : 0
% 3.47/1.54  #Split   : 0
% 3.47/1.54  #Chain   : 0
% 3.47/1.54  #Close   : 0
% 3.47/1.54  
% 3.47/1.54  Ordering : KBO
% 3.47/1.54  
% 3.47/1.54  Simplification rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Subsume      : 26
% 3.47/1.54  #Demod        : 22
% 3.47/1.54  #Tautology    : 69
% 3.47/1.54  #SimpNegUnit  : 0
% 3.47/1.54  #BackRed      : 0
% 3.47/1.54  
% 3.47/1.54  #Partial instantiations: 0
% 3.47/1.54  #Strategies tried      : 1
% 3.47/1.54  
% 3.47/1.54  Timing (in seconds)
% 3.47/1.54  ----------------------
% 3.47/1.54  Preprocessing        : 0.32
% 3.47/1.54  Parsing              : 0.17
% 3.47/1.54  CNF conversion       : 0.02
% 3.47/1.54  Main loop            : 0.45
% 3.47/1.54  Inferencing          : 0.17
% 3.47/1.54  Reduction            : 0.12
% 3.47/1.54  Demodulation         : 0.08
% 3.47/1.54  BG Simplification    : 0.04
% 3.47/1.54  Subsumption          : 0.09
% 3.47/1.54  Abstraction          : 0.04
% 3.47/1.54  MUC search           : 0.00
% 3.47/1.54  Cooper               : 0.00
% 3.47/1.54  Total                : 0.80
% 3.47/1.54  Index Insertion      : 0.00
% 3.47/1.54  Index Deletion       : 0.00
% 3.47/1.54  Index Matching       : 0.00
% 3.47/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
