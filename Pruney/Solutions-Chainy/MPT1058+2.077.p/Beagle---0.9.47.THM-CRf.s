%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:32 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   37 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  77 expanded)
%              Number of equality atoms :   30 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    ! [B_50,A_49] : k5_relat_1(k6_relat_1(B_50),k6_relat_1(A_49)) = k6_relat_1(k3_xboole_0(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_316,plain,(
    ! [A_90,B_91] :
      ( k10_relat_1(A_90,k1_relat_1(B_91)) = k1_relat_1(k5_relat_1(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_325,plain,(
    ! [A_90,A_45] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_45))) = k10_relat_1(A_90,A_45)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_316])).

tff(c_330,plain,(
    ! [A_92,A_93] :
      ( k1_relat_1(k5_relat_1(A_92,k6_relat_1(A_93))) = k10_relat_1(A_92,A_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_325])).

tff(c_342,plain,(
    ! [A_49,B_50] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_49,B_50))) = k10_relat_1(k6_relat_1(B_50),A_49)
      | ~ v1_relat_1(k6_relat_1(B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_330])).

tff(c_350,plain,(
    ! [B_50,A_49] : k10_relat_1(k6_relat_1(B_50),A_49) = k3_xboole_0(A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_342])).

tff(c_36,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_461,plain,(
    ! [B_105,C_106,A_107] :
      ( k10_relat_1(k5_relat_1(B_105,C_106),A_107) = k10_relat_1(B_105,k10_relat_1(C_106,A_107))
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_481,plain,(
    ! [A_46,B_47,A_107] :
      ( k10_relat_1(k6_relat_1(A_46),k10_relat_1(B_47,A_107)) = k10_relat_1(k7_relat_1(B_47,A_46),A_107)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_461])).

tff(c_1367,plain,(
    ! [B_145,A_146,A_147] :
      ( k3_xboole_0(k10_relat_1(B_145,A_146),A_147) = k10_relat_1(k7_relat_1(B_145,A_147),A_146)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_350,c_481])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_106,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_106])).

tff(c_141,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_141])).

tff(c_162,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_156])).

tff(c_1426,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1367,c_162])).

tff(c_1489,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1426])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.50  
% 3.36/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.50  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.36/1.50  
% 3.36/1.50  %Foreground sorts:
% 3.36/1.50  
% 3.36/1.50  
% 3.36/1.50  %Background operators:
% 3.36/1.50  
% 3.36/1.50  
% 3.36/1.50  %Foreground operators:
% 3.36/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.36/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.36/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.36/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.36/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.36/1.50  
% 3.36/1.51  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.36/1.51  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.36/1.51  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.36/1.51  tff(f_79, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.36/1.51  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.36/1.51  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.36/1.51  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 3.36/1.51  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.36/1.51  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.36/1.51  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.36/1.51  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.51  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.51  tff(c_38, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.36/1.51  tff(c_32, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.36/1.51  tff(c_42, plain, (![B_50, A_49]: (k5_relat_1(k6_relat_1(B_50), k6_relat_1(A_49))=k6_relat_1(k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.36/1.51  tff(c_316, plain, (![A_90, B_91]: (k10_relat_1(A_90, k1_relat_1(B_91))=k1_relat_1(k5_relat_1(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_325, plain, (![A_90, A_45]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_45)))=k10_relat_1(A_90, A_45) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_32, c_316])).
% 3.36/1.51  tff(c_330, plain, (![A_92, A_93]: (k1_relat_1(k5_relat_1(A_92, k6_relat_1(A_93)))=k10_relat_1(A_92, A_93) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_325])).
% 3.36/1.51  tff(c_342, plain, (![A_49, B_50]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_49, B_50)))=k10_relat_1(k6_relat_1(B_50), A_49) | ~v1_relat_1(k6_relat_1(B_50)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_330])).
% 3.36/1.51  tff(c_350, plain, (![B_50, A_49]: (k10_relat_1(k6_relat_1(B_50), A_49)=k3_xboole_0(A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_342])).
% 3.36/1.51  tff(c_36, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.36/1.51  tff(c_461, plain, (![B_105, C_106, A_107]: (k10_relat_1(k5_relat_1(B_105, C_106), A_107)=k10_relat_1(B_105, k10_relat_1(C_106, A_107)) | ~v1_relat_1(C_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.51  tff(c_481, plain, (![A_46, B_47, A_107]: (k10_relat_1(k6_relat_1(A_46), k10_relat_1(B_47, A_107))=k10_relat_1(k7_relat_1(B_47, A_46), A_107) | ~v1_relat_1(B_47) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_36, c_461])).
% 3.36/1.51  tff(c_1367, plain, (![B_145, A_146, A_147]: (k3_xboole_0(k10_relat_1(B_145, A_146), A_147)=k10_relat_1(k7_relat_1(B_145, A_147), A_146) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_350, c_481])).
% 3.36/1.51  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.51  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.51  tff(c_106, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.51  tff(c_114, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_106])).
% 3.36/1.51  tff(c_141, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.51  tff(c_156, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_114, c_141])).
% 3.36/1.51  tff(c_162, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_156])).
% 3.36/1.51  tff(c_1426, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1367, c_162])).
% 3.36/1.51  tff(c_1489, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1426])).
% 3.36/1.51  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1489])).
% 3.36/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  Inference rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Ref     : 0
% 3.36/1.51  #Sup     : 335
% 3.36/1.51  #Fact    : 0
% 3.36/1.51  #Define  : 0
% 3.36/1.51  #Split   : 0
% 3.36/1.51  #Chain   : 0
% 3.36/1.51  #Close   : 0
% 3.36/1.51  
% 3.36/1.51  Ordering : KBO
% 3.36/1.51  
% 3.36/1.51  Simplification rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Subsume      : 1
% 3.36/1.51  #Demod        : 334
% 3.36/1.51  #Tautology    : 242
% 3.36/1.51  #SimpNegUnit  : 1
% 3.36/1.51  #BackRed      : 2
% 3.36/1.51  
% 3.36/1.51  #Partial instantiations: 0
% 3.36/1.51  #Strategies tried      : 1
% 3.36/1.51  
% 3.36/1.51  Timing (in seconds)
% 3.36/1.51  ----------------------
% 3.36/1.52  Preprocessing        : 0.32
% 3.36/1.52  Parsing              : 0.18
% 3.36/1.52  CNF conversion       : 0.02
% 3.36/1.52  Main loop            : 0.43
% 3.36/1.52  Inferencing          : 0.16
% 3.36/1.52  Reduction            : 0.17
% 3.36/1.52  Demodulation         : 0.13
% 3.36/1.52  BG Simplification    : 0.02
% 3.36/1.52  Subsumption          : 0.06
% 3.36/1.52  Abstraction          : 0.03
% 3.36/1.52  MUC search           : 0.00
% 3.36/1.52  Cooper               : 0.00
% 3.36/1.52  Total                : 0.78
% 3.36/1.52  Index Insertion      : 0.00
% 3.36/1.52  Index Deletion       : 0.00
% 3.36/1.52  Index Matching       : 0.00
% 3.36/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
