%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 148 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 164 expanded)
%              Number of equality atoms :   52 ( 136 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_76,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_138,plain,(
    ! [A_47] : k2_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_353,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_388,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_353])).

tff(c_401,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30,c_388])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_459,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,k1_tarski(B_76)) = A_75
      | r2_hidden(B_76,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_476,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_80])).

tff(c_495,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_476])).

tff(c_66,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_331,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [E_29,B_24,C_25] : r2_hidden(E_29,k1_enumset1(E_29,B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_349,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_48])).

tff(c_352,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_349])).

tff(c_209,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(A_49,B_50)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_222,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_1526,plain,(
    ! [B_116,A_117] : k4_xboole_0(k4_xboole_0(B_116,A_117),k2_xboole_0(A_117,B_116)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_222])).

tff(c_1578,plain,(
    k4_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),'#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_1526])).

tff(c_74,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,k1_tarski(B_37)) = A_36
      | r2_hidden(B_37,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1771,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0
    | r2_hidden('#skF_4',k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_74])).

tff(c_4897,plain,(
    r2_hidden('#skF_4',k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1771])).

tff(c_1017,plain,(
    ! [A_104,B_105] : k2_xboole_0(k4_xboole_0(A_104,B_105),k4_xboole_0(B_105,A_104)) = k5_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1100,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) = k5_xboole_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1017])).

tff(c_1126,plain,(
    k5_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1100])).

tff(c_1910,plain,(
    ! [A_122,C_123,B_124] :
      ( ~ r2_hidden(A_122,C_123)
      | ~ r2_hidden(A_122,B_124)
      | ~ r2_hidden(A_122,k5_xboole_0(B_124,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1919,plain,(
    ! [A_122] :
      ( ~ r2_hidden(A_122,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_122,'#skF_3')
      | ~ r2_hidden(A_122,k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1126,c_1910])).

tff(c_4903,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4897,c_1919])).

tff(c_4909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_352,c_4903])).

tff(c_4910,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1771])).

tff(c_38,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_381,plain,(
    ! [A_19,B_20] : k2_xboole_0(k2_xboole_0(A_19,B_20),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_353])).

tff(c_810,plain,(
    ! [A_98,B_99] : k2_xboole_0(k2_xboole_0(A_98,B_99),A_98) = k2_xboole_0(A_98,B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_381])).

tff(c_870,plain,(
    ! [A_1,B_99] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_99)) = k2_xboole_0(A_1,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_810])).

tff(c_34,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_372,plain,(
    ! [A_1,B_2] : k2_xboole_0(k2_xboole_0(A_1,B_2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_1,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_353])).

tff(c_1399,plain,(
    ! [A_114,B_115] : k2_xboole_0(k2_xboole_0(A_114,B_115),B_115) = k2_xboole_0(A_114,B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_372])).

tff(c_2411,plain,(
    ! [A_136,B_137] : k2_xboole_0(k2_xboole_0(A_136,B_137),A_136) = k2_xboole_0(B_137,A_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1399])).

tff(c_2630,plain,(
    ! [B_142,B_143] : k2_xboole_0(B_142,k2_xboole_0(B_142,B_143)) = k2_xboole_0(B_143,B_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2411])).

tff(c_2746,plain,(
    ! [B_17,A_16] : k2_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k2_xboole_0(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2630])).

tff(c_2795,plain,(
    ! [B_17,A_16] : k2_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k2_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_2746])).

tff(c_4935,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_4')) = k2_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4910,c_2795])).

tff(c_4964,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_401,c_4935])).

tff(c_4966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:31:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/2.03  
% 5.01/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/2.03  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.01/2.03  
% 5.01/2.03  %Foreground sorts:
% 5.01/2.03  
% 5.01/2.03  
% 5.01/2.03  %Background operators:
% 5.01/2.03  
% 5.01/2.03  
% 5.01/2.03  %Foreground operators:
% 5.01/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.01/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/2.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.01/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.01/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/2.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.01/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.01/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.01/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.01/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/2.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.01/2.03  
% 5.22/2.05  tff(f_96, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 5.22/2.05  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.22/2.05  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.22/2.05  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.22/2.05  tff(f_86, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.22/2.05  tff(f_77, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.22/2.05  tff(f_79, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.22/2.05  tff(f_75, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.22/2.05  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.22/2.05  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.22/2.05  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.22/2.05  tff(c_76, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.22/2.05  tff(c_122, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.22/2.05  tff(c_30, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.22/2.05  tff(c_138, plain, (![A_47]: (k2_xboole_0(k1_xboole_0, A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_122, c_30])).
% 5.22/2.05  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.22/2.05  tff(c_80, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.22/2.05  tff(c_353, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.22/2.05  tff(c_388, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_80, c_353])).
% 5.22/2.05  tff(c_401, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30, c_388])).
% 5.22/2.05  tff(c_78, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.22/2.05  tff(c_459, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k1_tarski(B_76))=A_75 | r2_hidden(B_76, A_75))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.22/2.05  tff(c_476, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_459, c_80])).
% 5.22/2.05  tff(c_495, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_476])).
% 5.22/2.05  tff(c_66, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.22/2.05  tff(c_331, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.22/2.05  tff(c_48, plain, (![E_29, B_24, C_25]: (r2_hidden(E_29, k1_enumset1(E_29, B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.22/2.05  tff(c_349, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_331, c_48])).
% 5.22/2.05  tff(c_352, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_349])).
% 5.22/2.05  tff(c_209, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(A_49, B_50))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.22/2.05  tff(c_222, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_209])).
% 5.22/2.05  tff(c_1526, plain, (![B_116, A_117]: (k4_xboole_0(k4_xboole_0(B_116, A_117), k2_xboole_0(A_117, B_116))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_353, c_222])).
% 5.22/2.05  tff(c_1578, plain, (k4_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_401, c_1526])).
% 5.22/2.05  tff(c_74, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k1_tarski(B_37))=A_36 | r2_hidden(B_37, A_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.22/2.05  tff(c_1771, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0 | r2_hidden('#skF_4', k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1578, c_74])).
% 5.22/2.05  tff(c_4897, plain, (r2_hidden('#skF_4', k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1771])).
% 5.22/2.05  tff(c_1017, plain, (![A_104, B_105]: (k2_xboole_0(k4_xboole_0(A_104, B_105), k4_xboole_0(B_105, A_104))=k5_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.22/2.05  tff(c_1100, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'))=k5_xboole_0('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1017])).
% 5.22/2.05  tff(c_1126, plain, (k5_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1100])).
% 5.22/2.05  tff(c_1910, plain, (![A_122, C_123, B_124]: (~r2_hidden(A_122, C_123) | ~r2_hidden(A_122, B_124) | ~r2_hidden(A_122, k5_xboole_0(B_124, C_123)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.22/2.05  tff(c_1919, plain, (![A_122]: (~r2_hidden(A_122, k1_tarski('#skF_4')) | ~r2_hidden(A_122, '#skF_3') | ~r2_hidden(A_122, k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1126, c_1910])).
% 5.22/2.05  tff(c_4903, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4897, c_1919])).
% 5.22/2.05  tff(c_4909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_352, c_4903])).
% 5.22/2.05  tff(c_4910, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1771])).
% 5.22/2.05  tff(c_38, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.22/2.05  tff(c_381, plain, (![A_19, B_20]: (k2_xboole_0(k2_xboole_0(A_19, B_20), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_38, c_353])).
% 5.22/2.05  tff(c_810, plain, (![A_98, B_99]: (k2_xboole_0(k2_xboole_0(A_98, B_99), A_98)=k2_xboole_0(A_98, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_381])).
% 5.22/2.05  tff(c_870, plain, (![A_1, B_99]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_99))=k2_xboole_0(A_1, B_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_810])).
% 5.22/2.05  tff(c_34, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.22/2.05  tff(c_372, plain, (![A_1, B_2]: (k2_xboole_0(k2_xboole_0(A_1, B_2), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_1, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_222, c_353])).
% 5.22/2.05  tff(c_1399, plain, (![A_114, B_115]: (k2_xboole_0(k2_xboole_0(A_114, B_115), B_115)=k2_xboole_0(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_372])).
% 5.22/2.05  tff(c_2411, plain, (![A_136, B_137]: (k2_xboole_0(k2_xboole_0(A_136, B_137), A_136)=k2_xboole_0(B_137, A_136))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1399])).
% 5.22/2.05  tff(c_2630, plain, (![B_142, B_143]: (k2_xboole_0(B_142, k2_xboole_0(B_142, B_143))=k2_xboole_0(B_143, B_142))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2411])).
% 5.22/2.05  tff(c_2746, plain, (![B_17, A_16]: (k2_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k2_xboole_0(A_16, k2_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2630])).
% 5.22/2.05  tff(c_2795, plain, (![B_17, A_16]: (k2_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k2_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_2746])).
% 5.22/2.05  tff(c_4935, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_4'))=k2_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4910, c_2795])).
% 5.22/2.05  tff(c_4964, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_401, c_4935])).
% 5.22/2.05  tff(c_4966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_4964])).
% 5.22/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.05  
% 5.22/2.05  Inference rules
% 5.22/2.05  ----------------------
% 5.22/2.05  #Ref     : 0
% 5.22/2.05  #Sup     : 1210
% 5.22/2.05  #Fact    : 0
% 5.22/2.05  #Define  : 0
% 5.22/2.05  #Split   : 1
% 5.22/2.05  #Chain   : 0
% 5.22/2.05  #Close   : 0
% 5.22/2.05  
% 5.22/2.05  Ordering : KBO
% 5.22/2.05  
% 5.22/2.05  Simplification rules
% 5.22/2.05  ----------------------
% 5.22/2.05  #Subsume      : 42
% 5.22/2.05  #Demod        : 1427
% 5.22/2.05  #Tautology    : 865
% 5.22/2.05  #SimpNegUnit  : 26
% 5.22/2.05  #BackRed      : 9
% 5.22/2.05  
% 5.22/2.05  #Partial instantiations: 0
% 5.22/2.05  #Strategies tried      : 1
% 5.22/2.05  
% 5.22/2.05  Timing (in seconds)
% 5.22/2.05  ----------------------
% 5.22/2.05  Preprocessing        : 0.36
% 5.22/2.05  Parsing              : 0.17
% 5.22/2.05  CNF conversion       : 0.03
% 5.22/2.05  Main loop            : 0.86
% 5.22/2.05  Inferencing          : 0.24
% 5.25/2.05  Reduction            : 0.42
% 5.25/2.05  Demodulation         : 0.35
% 5.25/2.05  BG Simplification    : 0.03
% 5.25/2.05  Subsumption          : 0.12
% 5.25/2.05  Abstraction          : 0.04
% 5.25/2.05  MUC search           : 0.00
% 5.25/2.05  Cooper               : 0.00
% 5.25/2.05  Total                : 1.26
% 5.25/2.05  Index Insertion      : 0.00
% 5.25/2.05  Index Deletion       : 0.00
% 5.25/2.05  Index Matching       : 0.00
% 5.25/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
