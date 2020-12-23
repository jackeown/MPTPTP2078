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
% DateTime   : Thu Dec  3 09:52:11 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 123 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 137 expanded)
%              Number of equality atoms :   42 (  85 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_145])).

tff(c_161,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_157])).

tff(c_38,plain,(
    ! [B_50] : k4_xboole_0(k1_tarski(B_50),k1_tarski(B_50)) != k1_tarski(B_50) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_162,plain,(
    ! [B_50] : k1_tarski(B_50) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_38])).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_795,plain,(
    ! [A_106,B_107] :
      ( k4_xboole_0(k2_tarski(A_106,B_107),k1_tarski(B_107)) = k1_tarski(A_106)
      | B_107 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    ! [A_56,B_57] : r1_tarski(k3_xboole_0(A_56,B_57),A_56) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [B_57] : k3_xboole_0(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_16])).

tff(c_154,plain,(
    ! [B_57] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_145])).

tff(c_160,plain,(
    ! [B_57] : k4_xboole_0(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_154])).

tff(c_46,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_110,plain,(
    ! [B_61,A_62] :
      ( r1_xboole_0(B_61,A_62)
      | ~ r1_xboole_0(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    r1_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_110])).

tff(c_132,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_132])).

tff(c_383,plain,(
    ! [A_92,B_93,C_94] : k4_xboole_0(k3_xboole_0(A_92,B_93),C_94) = k3_xboole_0(A_92,k4_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_402,plain,(
    ! [C_94] : k3_xboole_0('#skF_3',k4_xboole_0(k2_tarski('#skF_1','#skF_2'),C_94)) = k4_xboole_0(k1_xboole_0,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_383])).

tff(c_419,plain,(
    ! [C_94] : k3_xboole_0('#skF_3',k4_xboole_0(k2_tarski('#skF_1','#skF_2'),C_94)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_402])).

tff(c_802,plain,
    ( k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_419])).

tff(c_820,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_826,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_143])).

tff(c_835,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_826])).

tff(c_36,plain,(
    ! [B_48,A_47] :
      ( k3_xboole_0(B_48,k1_tarski(A_47)) = k1_tarski(A_47)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_895,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_36])).

tff(c_911,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_895])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_911])).

tff(c_914,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_928,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_36])).

tff(c_944,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_928])).

tff(c_946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.39  
% 2.80/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.39  
% 2.80/1.39  %Foreground sorts:
% 2.80/1.39  
% 2.80/1.39  
% 2.80/1.39  %Background operators:
% 2.80/1.39  
% 2.80/1.39  
% 2.80/1.39  %Foreground operators:
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.39  
% 2.80/1.40  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.80/1.40  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.80/1.40  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.40  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.80/1.40  tff(f_83, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.80/1.40  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.40  tff(f_77, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.80/1.40  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.80/1.40  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.80/1.40  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.80/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.80/1.40  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.80/1.40  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.80/1.40  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.40  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.40  tff(c_145, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.40  tff(c_157, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_145])).
% 2.80/1.40  tff(c_161, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_157])).
% 2.80/1.40  tff(c_38, plain, (![B_50]: (k4_xboole_0(k1_tarski(B_50), k1_tarski(B_50))!=k1_tarski(B_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.40  tff(c_162, plain, (![B_50]: (k1_tarski(B_50)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_38])).
% 2.80/1.40  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.40  tff(c_22, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.40  tff(c_795, plain, (![A_106, B_107]: (k4_xboole_0(k2_tarski(A_106, B_107), k1_tarski(B_107))=k1_tarski(A_106) | B_107=A_106)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.80/1.40  tff(c_64, plain, (![A_56, B_57]: (r1_tarski(k3_xboole_0(A_56, B_57), A_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.40  tff(c_16, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.40  tff(c_72, plain, (![B_57]: (k3_xboole_0(k1_xboole_0, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_16])).
% 2.80/1.40  tff(c_154, plain, (![B_57]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_57))), inference(superposition, [status(thm), theory('equality')], [c_72, c_145])).
% 2.80/1.40  tff(c_160, plain, (![B_57]: (k4_xboole_0(k1_xboole_0, B_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_154])).
% 2.80/1.40  tff(c_46, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.40  tff(c_110, plain, (![B_61, A_62]: (r1_xboole_0(B_61, A_62) | ~r1_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.40  tff(c_113, plain, (r1_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_110])).
% 2.80/1.40  tff(c_132, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.40  tff(c_143, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_113, c_132])).
% 2.80/1.40  tff(c_383, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k3_xboole_0(A_92, B_93), C_94)=k3_xboole_0(A_92, k4_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.40  tff(c_402, plain, (![C_94]: (k3_xboole_0('#skF_3', k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), C_94))=k4_xboole_0(k1_xboole_0, C_94))), inference(superposition, [status(thm), theory('equality')], [c_143, c_383])).
% 2.80/1.40  tff(c_419, plain, (![C_94]: (k3_xboole_0('#skF_3', k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), C_94))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_402])).
% 2.80/1.40  tff(c_802, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_795, c_419])).
% 2.80/1.40  tff(c_820, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_802])).
% 2.80/1.40  tff(c_826, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_820, c_143])).
% 2.80/1.40  tff(c_835, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_826])).
% 2.80/1.40  tff(c_36, plain, (![B_48, A_47]: (k3_xboole_0(B_48, k1_tarski(A_47))=k1_tarski(A_47) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.40  tff(c_895, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_835, c_36])).
% 2.80/1.40  tff(c_911, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_895])).
% 2.80/1.40  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_911])).
% 2.80/1.40  tff(c_914, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_802])).
% 2.80/1.40  tff(c_928, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_914, c_36])).
% 2.80/1.40  tff(c_944, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_928])).
% 2.80/1.40  tff(c_946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_944])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 230
% 2.80/1.40  #Fact    : 0
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 1
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 5
% 2.80/1.40  #Demod        : 114
% 2.80/1.40  #Tautology    : 136
% 2.80/1.40  #SimpNegUnit  : 10
% 2.80/1.40  #BackRed      : 10
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.41  Preprocessing        : 0.31
% 2.80/1.41  Parsing              : 0.16
% 2.80/1.41  CNF conversion       : 0.02
% 2.80/1.41  Main loop            : 0.32
% 2.80/1.41  Inferencing          : 0.11
% 2.80/1.41  Reduction            : 0.11
% 2.80/1.41  Demodulation         : 0.09
% 2.80/1.41  BG Simplification    : 0.02
% 2.80/1.41  Subsumption          : 0.06
% 2.80/1.41  Abstraction          : 0.02
% 2.80/1.41  MUC search           : 0.00
% 2.80/1.41  Cooper               : 0.00
% 2.80/1.41  Total                : 0.66
% 2.80/1.41  Index Insertion      : 0.00
% 2.80/1.41  Index Deletion       : 0.00
% 2.80/1.41  Index Matching       : 0.00
% 2.80/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
