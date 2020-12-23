%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:36 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   64 (  72 expanded)
%              Number of leaves         :   32 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 (  86 expanded)
%              Number of equality atoms :   43 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_40,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_101,plain,(
    ! [A_55,B_56] : r1_tarski(k1_tarski(A_55),k2_tarski(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    ! [A_18] : r1_tarski(k1_tarski(A_18),k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_32,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_116,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_116])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,B_66)
      | ~ r1_tarski(A_65,k3_xboole_0(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [A_82,B_83,A_84] :
      ( r1_tarski(A_82,B_83)
      | ~ r1_tarski(A_82,k3_xboole_0(A_84,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_320,plain,(
    ! [A_89] :
      ( r1_tarski(A_89,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_89,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_265])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_347,plain,(
    ! [A_100] :
      ( k3_xboole_0(A_100,k2_tarski('#skF_3','#skF_4')) = A_100
      | ~ r1_tarski(A_100,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_320,c_10])).

tff(c_357,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_347])).

tff(c_137,plain,(
    ! [A_65,B_2,A_1] :
      ( r1_tarski(A_65,B_2)
      | ~ r1_tarski(A_65,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_361,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_65,k1_tarski('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_137])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_159,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_34,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_169,plain,(
    ! [B_49] : k1_tarski(B_49) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_34])).

tff(c_426,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_xboole_0(k1_enumset1(A_110,B_111,C_112),k1_tarski(A_110)) = k2_tarski(B_111,C_112)
      | C_112 = A_110
      | B_111 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_432,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_tarski(A_110) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_110),k2_tarski(B_111,C_112))
      | C_112 = A_110
      | B_111 = A_110 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_12])).

tff(c_443,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_tarski(k1_tarski(A_113),k2_tarski(B_114,C_115))
      | C_115 = A_113
      | B_114 = A_113 ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_432])).

tff(c_476,plain,(
    ! [A_122] :
      ( A_122 = '#skF_4'
      | A_122 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_122),k1_tarski('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_361,c_443])).

tff(c_480,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_104,c_476])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  
% 2.56/1.32  tff(f_86, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.56/1.32  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.32  tff(f_71, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.56/1.32  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.56/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.56/1.32  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.56/1.32  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.56/1.32  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.56/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.56/1.32  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.56/1.32  tff(f_55, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_enumset1)).
% 2.56/1.32  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.56/1.32  tff(c_40, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.56/1.32  tff(c_38, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.56/1.32  tff(c_18, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.32  tff(c_101, plain, (![A_55, B_56]: (r1_tarski(k1_tarski(A_55), k2_tarski(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.32  tff(c_104, plain, (![A_18]: (r1_tarski(k1_tarski(A_18), k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_101])).
% 2.56/1.32  tff(c_32, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.32  tff(c_42, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.56/1.32  tff(c_116, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.32  tff(c_126, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_116])).
% 2.56/1.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.32  tff(c_131, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, B_66) | ~r1_tarski(A_65, k3_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.32  tff(c_265, plain, (![A_82, B_83, A_84]: (r1_tarski(A_82, B_83) | ~r1_tarski(A_82, k3_xboole_0(A_84, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 2.56/1.32  tff(c_320, plain, (![A_89]: (r1_tarski(A_89, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_89, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_126, c_265])).
% 2.56/1.32  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.32  tff(c_347, plain, (![A_100]: (k3_xboole_0(A_100, k2_tarski('#skF_3', '#skF_4'))=A_100 | ~r1_tarski(A_100, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_320, c_10])).
% 2.56/1.32  tff(c_357, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_32, c_347])).
% 2.56/1.32  tff(c_137, plain, (![A_65, B_2, A_1]: (r1_tarski(A_65, B_2) | ~r1_tarski(A_65, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 2.56/1.32  tff(c_361, plain, (![A_65]: (r1_tarski(A_65, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_65, k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_357, c_137])).
% 2.56/1.32  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.32  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.32  tff(c_141, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.32  tff(c_156, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_141])).
% 2.56/1.32  tff(c_159, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_156])).
% 2.56/1.32  tff(c_34, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.56/1.32  tff(c_169, plain, (![B_49]: (k1_tarski(B_49)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_34])).
% 2.56/1.32  tff(c_426, plain, (![A_110, B_111, C_112]: (k4_xboole_0(k1_enumset1(A_110, B_111, C_112), k1_tarski(A_110))=k2_tarski(B_111, C_112) | C_112=A_110 | B_111=A_110)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.56/1.32  tff(c_12, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.56/1.32  tff(c_432, plain, (![A_110, B_111, C_112]: (k1_tarski(A_110)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_110), k2_tarski(B_111, C_112)) | C_112=A_110 | B_111=A_110)), inference(superposition, [status(thm), theory('equality')], [c_426, c_12])).
% 2.56/1.32  tff(c_443, plain, (![A_113, B_114, C_115]: (~r1_tarski(k1_tarski(A_113), k2_tarski(B_114, C_115)) | C_115=A_113 | B_114=A_113)), inference(negUnitSimplification, [status(thm)], [c_169, c_432])).
% 2.56/1.32  tff(c_476, plain, (![A_122]: (A_122='#skF_4' | A_122='#skF_3' | ~r1_tarski(k1_tarski(A_122), k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_361, c_443])).
% 2.56/1.32  tff(c_480, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_104, c_476])).
% 2.56/1.32  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_480])).
% 2.56/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.32  
% 2.56/1.32  Inference rules
% 2.56/1.32  ----------------------
% 2.56/1.32  #Ref     : 0
% 2.56/1.32  #Sup     : 109
% 2.56/1.32  #Fact    : 0
% 2.56/1.32  #Define  : 0
% 2.56/1.32  #Split   : 0
% 2.56/1.32  #Chain   : 0
% 2.56/1.32  #Close   : 0
% 2.56/1.32  
% 2.56/1.32  Ordering : KBO
% 2.56/1.32  
% 2.56/1.32  Simplification rules
% 2.56/1.32  ----------------------
% 2.56/1.32  #Subsume      : 9
% 2.56/1.32  #Demod        : 22
% 2.56/1.32  #Tautology    : 75
% 2.56/1.32  #SimpNegUnit  : 5
% 2.56/1.32  #BackRed      : 1
% 2.56/1.32  
% 2.56/1.32  #Partial instantiations: 0
% 2.56/1.32  #Strategies tried      : 1
% 2.56/1.32  
% 2.56/1.32  Timing (in seconds)
% 2.56/1.32  ----------------------
% 2.56/1.32  Preprocessing        : 0.31
% 2.56/1.32  Parsing              : 0.17
% 2.56/1.32  CNF conversion       : 0.02
% 2.56/1.32  Main loop            : 0.25
% 2.56/1.32  Inferencing          : 0.10
% 2.56/1.32  Reduction            : 0.08
% 2.56/1.32  Demodulation         : 0.06
% 2.56/1.32  BG Simplification    : 0.02
% 2.56/1.32  Subsumption          : 0.04
% 2.56/1.32  Abstraction          : 0.01
% 2.56/1.32  MUC search           : 0.00
% 2.56/1.32  Cooper               : 0.00
% 2.56/1.32  Total                : 0.59
% 2.56/1.32  Index Insertion      : 0.00
% 2.56/1.32  Index Deletion       : 0.00
% 2.56/1.32  Index Matching       : 0.00
% 2.56/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
