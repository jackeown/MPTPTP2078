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
% DateTime   : Thu Dec  3 10:04:31 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 100 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [A_50] : v1_relat_1(k6_relat_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_153,plain,(
    ! [B_72,A_73] :
      ( k7_relat_1(B_72,A_73) = B_72
      | ~ r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [A_45,A_73] :
      ( k7_relat_1(k6_relat_1(A_45),A_73) = k6_relat_1(A_45)
      | ~ r1_tarski(A_45,A_73)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_158,plain,(
    ! [A_45,A_73] :
      ( k7_relat_1(k6_relat_1(A_45),A_73) = k6_relat_1(A_45)
      | ~ r1_tarski(A_45,A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_32,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_257,plain,(
    ! [A_88,B_89] :
      ( k10_relat_1(A_88,k1_relat_1(B_89)) = k1_relat_1(k5_relat_1(A_88,B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_266,plain,(
    ! [A_88,A_45] :
      ( k1_relat_1(k5_relat_1(A_88,k6_relat_1(A_45))) = k10_relat_1(A_88,A_45)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_257])).

tff(c_271,plain,(
    ! [A_90,A_91] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_91))) = k10_relat_1(A_90,A_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_266])).

tff(c_287,plain,(
    ! [A_91,A_46] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_91),A_46)) = k10_relat_1(k6_relat_1(A_46),A_91)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_271])).

tff(c_292,plain,(
    ! [A_92,A_93] : k1_relat_1(k7_relat_1(k6_relat_1(A_92),A_93)) = k10_relat_1(k6_relat_1(A_93),A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_287])).

tff(c_307,plain,(
    ! [A_73,A_45] :
      ( k10_relat_1(k6_relat_1(A_73),A_45) = k1_relat_1(k6_relat_1(A_45))
      | ~ r1_tarski(A_45,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_292])).

tff(c_320,plain,(
    ! [A_99,A_100] :
      ( k10_relat_1(k6_relat_1(A_99),A_100) = A_100
      | ~ r1_tarski(A_100,A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_307])).

tff(c_30,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_215,plain,(
    ! [B_84,A_85] :
      ( k10_relat_1(B_84,k3_xboole_0(k2_relat_1(B_84),A_85)) = k10_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_232,plain,(
    ! [A_45,A_85] :
      ( k10_relat_1(k6_relat_1(A_45),k3_xboole_0(A_45,A_85)) = k10_relat_1(k6_relat_1(A_45),A_85)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_215])).

tff(c_238,plain,(
    ! [A_45,A_85] : k10_relat_1(k6_relat_1(A_45),k3_xboole_0(A_45,A_85)) = k10_relat_1(k6_relat_1(A_45),A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_232])).

tff(c_331,plain,(
    ! [A_99,A_85] :
      ( k10_relat_1(k6_relat_1(A_99),A_85) = k3_xboole_0(A_99,A_85)
      | ~ r1_tarski(k3_xboole_0(A_99,A_85),A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_238])).

tff(c_354,plain,(
    ! [A_99,A_85] : k10_relat_1(k6_relat_1(A_99),A_85) = k3_xboole_0(A_99,A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_331])).

tff(c_401,plain,(
    ! [B_103,C_104,A_105] :
      ( k10_relat_1(k5_relat_1(B_103,C_104),A_105) = k10_relat_1(B_103,k10_relat_1(C_104,A_105))
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_426,plain,(
    ! [A_46,B_47,A_105] :
      ( k10_relat_1(k6_relat_1(A_46),k10_relat_1(B_47,A_105)) = k10_relat_1(k7_relat_1(B_47,A_46),A_105)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_401])).

tff(c_563,plain,(
    ! [A_129,B_130,A_131] :
      ( k3_xboole_0(A_129,k10_relat_1(B_130,A_131)) = k10_relat_1(k7_relat_1(B_130,A_129),A_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_354,c_426])).

tff(c_40,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_582,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_40])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.73/1.42  
% 2.73/1.42  %Foreground sorts:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Background operators:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Foreground operators:
% 2.73/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.73/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.73/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.42  
% 2.73/1.43  tff(f_86, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.73/1.43  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.73/1.43  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.73/1.43  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.73/1.43  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.73/1.43  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.73/1.43  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.73/1.43  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.73/1.43  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.73/1.43  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.43  tff(c_36, plain, (![A_50]: (v1_relat_1(k6_relat_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.73/1.43  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.43  tff(c_28, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.43  tff(c_153, plain, (![B_72, A_73]: (k7_relat_1(B_72, A_73)=B_72 | ~r1_tarski(k1_relat_1(B_72), A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.43  tff(c_156, plain, (![A_45, A_73]: (k7_relat_1(k6_relat_1(A_45), A_73)=k6_relat_1(A_45) | ~r1_tarski(A_45, A_73) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_153])).
% 2.73/1.43  tff(c_158, plain, (![A_45, A_73]: (k7_relat_1(k6_relat_1(A_45), A_73)=k6_relat_1(A_45) | ~r1_tarski(A_45, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_156])).
% 2.73/1.43  tff(c_32, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.73/1.43  tff(c_257, plain, (![A_88, B_89]: (k10_relat_1(A_88, k1_relat_1(B_89))=k1_relat_1(k5_relat_1(A_88, B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.43  tff(c_266, plain, (![A_88, A_45]: (k1_relat_1(k5_relat_1(A_88, k6_relat_1(A_45)))=k10_relat_1(A_88, A_45) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_28, c_257])).
% 2.73/1.43  tff(c_271, plain, (![A_90, A_91]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_91)))=k10_relat_1(A_90, A_91) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_266])).
% 2.73/1.43  tff(c_287, plain, (![A_91, A_46]: (k1_relat_1(k7_relat_1(k6_relat_1(A_91), A_46))=k10_relat_1(k6_relat_1(A_46), A_91) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_91)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_271])).
% 2.73/1.43  tff(c_292, plain, (![A_92, A_93]: (k1_relat_1(k7_relat_1(k6_relat_1(A_92), A_93))=k10_relat_1(k6_relat_1(A_93), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_287])).
% 2.73/1.43  tff(c_307, plain, (![A_73, A_45]: (k10_relat_1(k6_relat_1(A_73), A_45)=k1_relat_1(k6_relat_1(A_45)) | ~r1_tarski(A_45, A_73))), inference(superposition, [status(thm), theory('equality')], [c_158, c_292])).
% 2.73/1.43  tff(c_320, plain, (![A_99, A_100]: (k10_relat_1(k6_relat_1(A_99), A_100)=A_100 | ~r1_tarski(A_100, A_99))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_307])).
% 2.73/1.43  tff(c_30, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.43  tff(c_215, plain, (![B_84, A_85]: (k10_relat_1(B_84, k3_xboole_0(k2_relat_1(B_84), A_85))=k10_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.43  tff(c_232, plain, (![A_45, A_85]: (k10_relat_1(k6_relat_1(A_45), k3_xboole_0(A_45, A_85))=k10_relat_1(k6_relat_1(A_45), A_85) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_215])).
% 2.73/1.43  tff(c_238, plain, (![A_45, A_85]: (k10_relat_1(k6_relat_1(A_45), k3_xboole_0(A_45, A_85))=k10_relat_1(k6_relat_1(A_45), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_232])).
% 2.73/1.43  tff(c_331, plain, (![A_99, A_85]: (k10_relat_1(k6_relat_1(A_99), A_85)=k3_xboole_0(A_99, A_85) | ~r1_tarski(k3_xboole_0(A_99, A_85), A_99))), inference(superposition, [status(thm), theory('equality')], [c_320, c_238])).
% 2.73/1.43  tff(c_354, plain, (![A_99, A_85]: (k10_relat_1(k6_relat_1(A_99), A_85)=k3_xboole_0(A_99, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_331])).
% 2.73/1.43  tff(c_401, plain, (![B_103, C_104, A_105]: (k10_relat_1(k5_relat_1(B_103, C_104), A_105)=k10_relat_1(B_103, k10_relat_1(C_104, A_105)) | ~v1_relat_1(C_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.43  tff(c_426, plain, (![A_46, B_47, A_105]: (k10_relat_1(k6_relat_1(A_46), k10_relat_1(B_47, A_105))=k10_relat_1(k7_relat_1(B_47, A_46), A_105) | ~v1_relat_1(B_47) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_32, c_401])).
% 2.73/1.43  tff(c_563, plain, (![A_129, B_130, A_131]: (k3_xboole_0(A_129, k10_relat_1(B_130, A_131))=k10_relat_1(k7_relat_1(B_130, A_129), A_131) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_354, c_426])).
% 2.73/1.43  tff(c_40, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.43  tff(c_582, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_563, c_40])).
% 2.73/1.43  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_582])).
% 2.73/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  Inference rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Ref     : 0
% 2.73/1.43  #Sup     : 128
% 2.73/1.43  #Fact    : 0
% 2.73/1.44  #Define  : 0
% 2.73/1.44  #Split   : 0
% 2.73/1.44  #Chain   : 0
% 2.73/1.44  #Close   : 0
% 2.73/1.44  
% 2.73/1.44  Ordering : KBO
% 2.73/1.44  
% 2.73/1.44  Simplification rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Subsume      : 2
% 2.73/1.44  #Demod        : 85
% 2.73/1.44  #Tautology    : 86
% 2.73/1.44  #SimpNegUnit  : 0
% 2.73/1.44  #BackRed      : 3
% 2.73/1.44  
% 2.73/1.44  #Partial instantiations: 0
% 2.73/1.44  #Strategies tried      : 1
% 2.73/1.44  
% 2.73/1.44  Timing (in seconds)
% 2.73/1.44  ----------------------
% 2.73/1.44  Preprocessing        : 0.33
% 2.73/1.44  Parsing              : 0.18
% 2.73/1.44  CNF conversion       : 0.02
% 2.73/1.44  Main loop            : 0.25
% 2.73/1.44  Inferencing          : 0.11
% 2.73/1.44  Reduction            : 0.09
% 2.73/1.44  Demodulation         : 0.07
% 2.73/1.44  BG Simplification    : 0.02
% 2.73/1.44  Subsumption          : 0.03
% 2.73/1.44  Abstraction          : 0.02
% 2.73/1.44  MUC search           : 0.00
% 2.73/1.44  Cooper               : 0.00
% 2.73/1.44  Total                : 0.61
% 2.73/1.44  Index Insertion      : 0.00
% 2.73/1.44  Index Deletion       : 0.00
% 2.73/1.44  Index Matching       : 0.00
% 2.73/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
