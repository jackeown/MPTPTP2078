%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 128 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_83,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_114,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_24,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_198,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_69),k1_relat_1(B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_204,plain,(
    ! [A_29,B_70] :
      ( k5_relat_1(k6_relat_1(A_29),B_70) = k1_xboole_0
      | ~ r1_xboole_0(A_29,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_198])).

tff(c_222,plain,(
    ! [A_71,B_72] :
      ( k5_relat_1(k6_relat_1(A_71),B_72) = k1_xboole_0
      | ~ r1_xboole_0(A_71,k1_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_204])).

tff(c_228,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_222])).

tff(c_241,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_228])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_250,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_38])).

tff(c_257,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_250])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_257])).

tff(c_260,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_262,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_262])).

tff(c_273,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_36,plain,(
    ! [B_31,A_30] :
      ( k3_xboole_0(k1_relat_1(B_31),A_30) = k1_relat_1(k7_relat_1(B_31,A_30))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_367,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,k3_xboole_0(B_95,C_96))
      | ~ r1_tarski(A_94,C_96)
      | r1_xboole_0(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_609,plain,(
    ! [A_117,B_118,A_119] :
      ( ~ r1_xboole_0(A_117,k1_relat_1(k7_relat_1(B_118,A_119)))
      | ~ r1_tarski(A_117,A_119)
      | r1_xboole_0(A_117,k1_relat_1(B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_367])).

tff(c_628,plain,(
    ! [A_117] :
      ( ~ r1_xboole_0(A_117,k1_relat_1(k1_xboole_0))
      | ~ r1_tarski(A_117,'#skF_1')
      | r1_xboole_0(A_117,k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_609])).

tff(c_678,plain,(
    ! [A_122] :
      ( ~ r1_tarski(A_122,'#skF_1')
      | r1_xboole_0(A_122,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10,c_28,c_628])).

tff(c_700,plain,(
    ! [A_123] :
      ( r1_xboole_0(k1_relat_1('#skF_2'),A_123)
      | ~ r1_tarski(A_123,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_678,c_2])).

tff(c_274,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_715,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_700,c_274])).

tff(c_724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.56  
% 2.94/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.57  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.94/1.57  
% 2.94/1.57  %Foreground sorts:
% 2.94/1.57  
% 2.94/1.57  
% 2.94/1.57  %Background operators:
% 2.94/1.57  
% 2.94/1.57  
% 2.94/1.57  %Foreground operators:
% 2.94/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.94/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.94/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.94/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.94/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.94/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.94/1.57  
% 2.94/1.58  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.58  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.94/1.58  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.94/1.58  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.94/1.58  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.94/1.58  tff(f_57, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.94/1.58  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.94/1.58  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.94/1.58  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.94/1.58  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.94/1.58  tff(f_45, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.94/1.58  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.58  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.94/1.58  tff(c_10, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.58  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.94/1.58  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.94/1.58  tff(c_83, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.94/1.58  tff(c_48, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.94/1.58  tff(c_114, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_83, c_48])).
% 2.94/1.58  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.58  tff(c_117, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_2])).
% 2.94/1.58  tff(c_24, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.94/1.58  tff(c_34, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.58  tff(c_198, plain, (![A_69, B_70]: (k5_relat_1(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_69), k1_relat_1(B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.94/1.58  tff(c_204, plain, (![A_29, B_70]: (k5_relat_1(k6_relat_1(A_29), B_70)=k1_xboole_0 | ~r1_xboole_0(A_29, k1_relat_1(B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_198])).
% 2.94/1.58  tff(c_222, plain, (![A_71, B_72]: (k5_relat_1(k6_relat_1(A_71), B_72)=k1_xboole_0 | ~r1_xboole_0(A_71, k1_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_204])).
% 2.94/1.58  tff(c_228, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_117, c_222])).
% 2.94/1.58  tff(c_241, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_228])).
% 2.94/1.58  tff(c_38, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.94/1.58  tff(c_250, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_241, c_38])).
% 2.94/1.58  tff(c_257, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_250])).
% 2.94/1.58  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_257])).
% 2.94/1.58  tff(c_260, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 2.94/1.58  tff(c_262, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 2.94/1.58  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_262])).
% 2.94/1.58  tff(c_273, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.94/1.58  tff(c_36, plain, (![B_31, A_30]: (k3_xboole_0(k1_relat_1(B_31), A_30)=k1_relat_1(k7_relat_1(B_31, A_30)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.58  tff(c_367, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, k3_xboole_0(B_95, C_96)) | ~r1_tarski(A_94, C_96) | r1_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.58  tff(c_609, plain, (![A_117, B_118, A_119]: (~r1_xboole_0(A_117, k1_relat_1(k7_relat_1(B_118, A_119))) | ~r1_tarski(A_117, A_119) | r1_xboole_0(A_117, k1_relat_1(B_118)) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_36, c_367])).
% 2.94/1.58  tff(c_628, plain, (![A_117]: (~r1_xboole_0(A_117, k1_relat_1(k1_xboole_0)) | ~r1_tarski(A_117, '#skF_1') | r1_xboole_0(A_117, k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_609])).
% 2.94/1.58  tff(c_678, plain, (![A_122]: (~r1_tarski(A_122, '#skF_1') | r1_xboole_0(A_122, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10, c_28, c_628])).
% 2.94/1.58  tff(c_700, plain, (![A_123]: (r1_xboole_0(k1_relat_1('#skF_2'), A_123) | ~r1_tarski(A_123, '#skF_1'))), inference(resolution, [status(thm)], [c_678, c_2])).
% 2.94/1.58  tff(c_274, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 2.94/1.58  tff(c_715, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_700, c_274])).
% 2.94/1.58  tff(c_724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_715])).
% 2.94/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.58  
% 2.94/1.58  Inference rules
% 2.94/1.58  ----------------------
% 2.94/1.58  #Ref     : 0
% 2.94/1.58  #Sup     : 149
% 2.94/1.58  #Fact    : 0
% 2.94/1.58  #Define  : 0
% 2.94/1.58  #Split   : 4
% 2.94/1.58  #Chain   : 0
% 2.94/1.58  #Close   : 0
% 2.94/1.58  
% 2.94/1.58  Ordering : KBO
% 2.94/1.58  
% 2.94/1.58  Simplification rules
% 2.94/1.58  ----------------------
% 2.94/1.58  #Subsume      : 14
% 2.94/1.58  #Demod        : 65
% 2.94/1.58  #Tautology    : 81
% 2.94/1.58  #SimpNegUnit  : 3
% 2.94/1.58  #BackRed      : 0
% 2.94/1.58  
% 2.94/1.58  #Partial instantiations: 0
% 2.94/1.58  #Strategies tried      : 1
% 2.94/1.58  
% 2.94/1.58  Timing (in seconds)
% 2.94/1.58  ----------------------
% 2.94/1.59  Preprocessing        : 0.36
% 2.94/1.59  Parsing              : 0.18
% 2.94/1.59  CNF conversion       : 0.02
% 2.94/1.59  Main loop            : 0.42
% 2.94/1.59  Inferencing          : 0.16
% 2.94/1.59  Reduction            : 0.13
% 2.94/1.59  Demodulation         : 0.10
% 2.94/1.59  BG Simplification    : 0.02
% 2.94/1.59  Subsumption          : 0.07
% 2.94/1.59  Abstraction          : 0.03
% 2.94/1.59  MUC search           : 0.00
% 2.94/1.59  Cooper               : 0.00
% 2.94/1.59  Total                : 0.83
% 2.94/1.59  Index Insertion      : 0.00
% 2.94/1.59  Index Deletion       : 0.00
% 2.94/1.59  Index Matching       : 0.00
% 2.94/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
