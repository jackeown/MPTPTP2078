%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:52 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   65 (  89 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_94,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_94])).

tff(c_18,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [A_51] :
      ( k7_relat_1(A_51,k1_relat_1(A_51)) = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_133,plain,(
    ! [A_30] :
      ( k7_relat_1(k6_relat_1(A_30),A_30) = k6_relat_1(A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_121])).

tff(c_137,plain,(
    ! [A_30] : k7_relat_1(k6_relat_1(A_30),A_30) = k6_relat_1(A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_133])).

tff(c_152,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_53,A_54)),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    ! [A_30] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_30)),A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_152])).

tff(c_169,plain,(
    ! [A_58] : r1_tarski(A_58,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24,c_158])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_573,plain,(
    ! [B_88,A_89] :
      ( k7_relat_1(B_88,A_89) = B_88
      | ~ r1_tarski(k1_relat_1(B_88),A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_654,plain,(
    ! [B_92,B_93] :
      ( k7_relat_1(B_92,k2_xboole_0(k1_relat_1(B_92),B_93)) = B_92
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_177,c_573])).

tff(c_691,plain,(
    ! [A_30,B_93] :
      ( k7_relat_1(k6_relat_1(A_30),k2_xboole_0(A_30,B_93)) = k6_relat_1(A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_654])).

tff(c_704,plain,(
    ! [A_94,B_95] : k7_relat_1(k6_relat_1(A_94),k2_xboole_0(A_94,B_95)) = k6_relat_1(A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_691])).

tff(c_744,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_704])).

tff(c_836,plain,(
    ! [B_97,A_98] :
      ( k3_xboole_0(k1_relat_1(B_97),A_98) = k1_relat_1(k7_relat_1(B_97,A_98))
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_859,plain,(
    ! [A_30,A_98] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_30),A_98)) = k3_xboole_0(A_30,A_98)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_836])).

tff(c_864,plain,(
    ! [A_99,A_100] : k1_relat_1(k7_relat_1(k6_relat_1(A_99),A_100)) = k3_xboole_0(A_99,A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_859])).

tff(c_894,plain,(
    k1_relat_1(k6_relat_1('#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_864])).

tff(c_919,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_894])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1170,plain,(
    ! [C_117,A_118,B_119] :
      ( k7_relat_1(k7_relat_1(C_117,A_118),B_119) = k7_relat_1(C_117,k3_xboole_0(A_118,B_119))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1193,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_36])).

tff(c_1235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_919,c_2,c_1193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.34  % Computer   : n007.cluster.edu
% 0.16/0.34  % Model      : x86_64 x86_64
% 0.16/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.34  % Memory     : 8042.1875MB
% 0.16/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.34  % CPULimit   : 60
% 0.16/0.34  % DateTime   : Tue Dec  1 17:11:51 EST 2020
% 0.16/0.34  % CPUTime    : 
% 0.16/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.42  
% 2.84/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.42  %$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.84/1.42  
% 2.84/1.42  %Foreground sorts:
% 2.84/1.42  
% 2.84/1.42  
% 2.84/1.42  %Background operators:
% 2.84/1.42  
% 2.84/1.42  
% 2.84/1.42  %Foreground operators:
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.84/1.42  
% 2.84/1.43  tff(f_84, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.84/1.43  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.84/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.84/1.43  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.84/1.43  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.84/1.43  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.84/1.43  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.84/1.43  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.84/1.43  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.84/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.84/1.43  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.84/1.43  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.84/1.43  tff(c_24, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.43  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.84/1.43  tff(c_94, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.43  tff(c_98, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_94])).
% 2.84/1.43  tff(c_18, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.43  tff(c_121, plain, (![A_51]: (k7_relat_1(A_51, k1_relat_1(A_51))=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.43  tff(c_133, plain, (![A_30]: (k7_relat_1(k6_relat_1(A_30), A_30)=k6_relat_1(A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_121])).
% 2.84/1.43  tff(c_137, plain, (![A_30]: (k7_relat_1(k6_relat_1(A_30), A_30)=k6_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_133])).
% 2.84/1.43  tff(c_152, plain, (![B_53, A_54]: (r1_tarski(k1_relat_1(k7_relat_1(B_53, A_54)), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.84/1.43  tff(c_158, plain, (![A_30]: (r1_tarski(k1_relat_1(k6_relat_1(A_30)), A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_152])).
% 2.84/1.43  tff(c_169, plain, (![A_58]: (r1_tarski(A_58, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24, c_158])).
% 2.84/1.43  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.43  tff(c_177, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_169, c_4])).
% 2.84/1.43  tff(c_573, plain, (![B_88, A_89]: (k7_relat_1(B_88, A_89)=B_88 | ~r1_tarski(k1_relat_1(B_88), A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.43  tff(c_654, plain, (![B_92, B_93]: (k7_relat_1(B_92, k2_xboole_0(k1_relat_1(B_92), B_93))=B_92 | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_177, c_573])).
% 2.84/1.43  tff(c_691, plain, (![A_30, B_93]: (k7_relat_1(k6_relat_1(A_30), k2_xboole_0(A_30, B_93))=k6_relat_1(A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_654])).
% 2.84/1.43  tff(c_704, plain, (![A_94, B_95]: (k7_relat_1(k6_relat_1(A_94), k2_xboole_0(A_94, B_95))=k6_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_691])).
% 2.84/1.43  tff(c_744, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_98, c_704])).
% 2.84/1.43  tff(c_836, plain, (![B_97, A_98]: (k3_xboole_0(k1_relat_1(B_97), A_98)=k1_relat_1(k7_relat_1(B_97, A_98)) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.43  tff(c_859, plain, (![A_30, A_98]: (k1_relat_1(k7_relat_1(k6_relat_1(A_30), A_98))=k3_xboole_0(A_30, A_98) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_836])).
% 2.84/1.43  tff(c_864, plain, (![A_99, A_100]: (k1_relat_1(k7_relat_1(k6_relat_1(A_99), A_100))=k3_xboole_0(A_99, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_859])).
% 2.84/1.43  tff(c_894, plain, (k1_relat_1(k6_relat_1('#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_744, c_864])).
% 2.84/1.43  tff(c_919, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_894])).
% 2.84/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.43  tff(c_1170, plain, (![C_117, A_118, B_119]: (k7_relat_1(k7_relat_1(C_117, A_118), B_119)=k7_relat_1(C_117, k3_xboole_0(A_118, B_119)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.43  tff(c_36, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.84/1.43  tff(c_1193, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1170, c_36])).
% 2.84/1.43  tff(c_1235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_919, c_2, c_1193])).
% 2.84/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  Inference rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Ref     : 0
% 2.84/1.43  #Sup     : 277
% 2.84/1.43  #Fact    : 0
% 2.84/1.43  #Define  : 0
% 2.84/1.43  #Split   : 0
% 2.84/1.43  #Chain   : 0
% 2.84/1.43  #Close   : 0
% 2.84/1.43  
% 2.84/1.43  Ordering : KBO
% 2.84/1.43  
% 2.84/1.43  Simplification rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Subsume      : 10
% 2.84/1.43  #Demod        : 182
% 2.84/1.43  #Tautology    : 176
% 2.84/1.43  #SimpNegUnit  : 0
% 2.84/1.43  #BackRed      : 0
% 2.84/1.43  
% 2.84/1.43  #Partial instantiations: 0
% 2.84/1.43  #Strategies tried      : 1
% 2.84/1.43  
% 2.84/1.43  Timing (in seconds)
% 2.84/1.43  ----------------------
% 2.84/1.44  Preprocessing        : 0.31
% 2.84/1.44  Parsing              : 0.17
% 2.84/1.44  CNF conversion       : 0.02
% 2.84/1.44  Main loop            : 0.36
% 2.84/1.44  Inferencing          : 0.14
% 2.84/1.44  Reduction            : 0.13
% 2.84/1.44  Demodulation         : 0.10
% 2.84/1.44  BG Simplification    : 0.02
% 2.84/1.44  Subsumption          : 0.05
% 2.84/1.44  Abstraction          : 0.02
% 2.84/1.44  MUC search           : 0.00
% 2.84/1.44  Cooper               : 0.00
% 2.84/1.44  Total                : 0.70
% 2.84/1.44  Index Insertion      : 0.00
% 2.84/1.44  Index Deletion       : 0.00
% 2.84/1.44  Index Matching       : 0.00
% 2.84/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
