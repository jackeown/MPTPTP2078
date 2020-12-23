%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   48 (  72 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24,D_25] : k3_enumset1(A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,E_30) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_176,plain,(
    ! [C_95,E_91,A_92,F_94,B_90,D_93] : k2_xboole_0(k3_enumset1(A_92,B_90,C_95,D_93,E_91),k1_tarski(F_94)) = k4_enumset1(A_92,B_90,C_95,D_93,E_91,F_94) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_185,plain,(
    ! [F_94,A_22,B_23,D_25,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,D_25,F_94) = k2_xboole_0(k2_enumset1(A_22,B_23,C_24,D_25),k1_tarski(F_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_176])).

tff(c_189,plain,(
    ! [A_96,C_97,B_100,D_98,F_99] : k2_xboole_0(k2_enumset1(A_96,B_100,C_97,D_98),k1_tarski(F_99)) = k3_enumset1(A_96,B_100,C_97,D_98,F_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_185])).

tff(c_198,plain,(
    ! [A_19,B_20,C_21,F_99] : k3_enumset1(A_19,A_19,B_20,C_21,F_99) = k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(F_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_189])).

tff(c_202,plain,(
    ! [A_101,B_102,C_103,F_104] : k2_xboole_0(k1_enumset1(A_101,B_102,C_103),k1_tarski(F_104)) = k2_enumset1(A_101,B_102,C_103,F_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_198])).

tff(c_211,plain,(
    ! [A_17,B_18,F_104] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(F_104)) = k2_enumset1(A_17,A_17,B_18,F_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_202])).

tff(c_215,plain,(
    ! [A_105,B_106,F_107] : k2_xboole_0(k2_tarski(A_105,B_106),k1_tarski(F_107)) = k1_enumset1(A_105,B_106,F_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_211])).

tff(c_224,plain,(
    ! [A_16,F_107] : k2_xboole_0(k1_tarski(A_16),k1_tarski(F_107)) = k1_enumset1(A_16,A_16,F_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_215])).

tff(c_228,plain,(
    ! [A_108,F_109] : k2_xboole_0(k1_tarski(A_108),k1_tarski(F_109)) = k2_tarski(A_108,F_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_224])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_234,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_46])).

tff(c_63,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [B_55,A_54] : r2_hidden(B_55,k2_tarski(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_255,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_69])).

tff(c_119,plain,(
    ! [E_70,C_71,B_72,A_73] :
      ( E_70 = C_71
      | E_70 = B_72
      | E_70 = A_73
      | ~ r2_hidden(E_70,k1_enumset1(A_73,B_72,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_147,plain,(
    ! [E_79,B_80,A_81] :
      ( E_79 = B_80
      | E_79 = A_81
      | E_79 = A_81
      | ~ r2_hidden(E_79,k2_tarski(A_81,B_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_119])).

tff(c_156,plain,(
    ! [E_79,A_16] :
      ( E_79 = A_16
      | E_79 = A_16
      | E_79 = A_16
      | ~ r2_hidden(E_79,k1_tarski(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_147])).

tff(c_272,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_255,c_156])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_44,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  
% 2.27/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.27/1.36  
% 2.27/1.36  %Foreground sorts:
% 2.27/1.36  
% 2.27/1.36  
% 2.27/1.36  %Background operators:
% 2.27/1.36  
% 2.27/1.36  
% 2.27/1.36  %Foreground operators:
% 2.27/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.27/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.27/1.36  
% 2.36/1.38  tff(f_63, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.36/1.38  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.36/1.38  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.38  tff(f_50, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.36/1.38  tff(f_52, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.36/1.38  tff(f_54, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.36/1.38  tff(f_44, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.36/1.38  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.36/1.38  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.38  tff(c_32, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.38  tff(c_30, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.38  tff(c_34, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.36/1.38  tff(c_36, plain, (![A_22, B_23, C_24, D_25]: (k3_enumset1(A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.36/1.38  tff(c_38, plain, (![B_27, D_29, A_26, E_30, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, E_30)=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.38  tff(c_176, plain, (![C_95, E_91, A_92, F_94, B_90, D_93]: (k2_xboole_0(k3_enumset1(A_92, B_90, C_95, D_93, E_91), k1_tarski(F_94))=k4_enumset1(A_92, B_90, C_95, D_93, E_91, F_94))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.38  tff(c_185, plain, (![F_94, A_22, B_23, D_25, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, D_25, F_94)=k2_xboole_0(k2_enumset1(A_22, B_23, C_24, D_25), k1_tarski(F_94)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_176])).
% 2.36/1.38  tff(c_189, plain, (![A_96, C_97, B_100, D_98, F_99]: (k2_xboole_0(k2_enumset1(A_96, B_100, C_97, D_98), k1_tarski(F_99))=k3_enumset1(A_96, B_100, C_97, D_98, F_99))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_185])).
% 2.36/1.38  tff(c_198, plain, (![A_19, B_20, C_21, F_99]: (k3_enumset1(A_19, A_19, B_20, C_21, F_99)=k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(F_99)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_189])).
% 2.36/1.38  tff(c_202, plain, (![A_101, B_102, C_103, F_104]: (k2_xboole_0(k1_enumset1(A_101, B_102, C_103), k1_tarski(F_104))=k2_enumset1(A_101, B_102, C_103, F_104))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_198])).
% 2.36/1.38  tff(c_211, plain, (![A_17, B_18, F_104]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(F_104))=k2_enumset1(A_17, A_17, B_18, F_104))), inference(superposition, [status(thm), theory('equality')], [c_32, c_202])).
% 2.36/1.38  tff(c_215, plain, (![A_105, B_106, F_107]: (k2_xboole_0(k2_tarski(A_105, B_106), k1_tarski(F_107))=k1_enumset1(A_105, B_106, F_107))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_211])).
% 2.36/1.38  tff(c_224, plain, (![A_16, F_107]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(F_107))=k1_enumset1(A_16, A_16, F_107))), inference(superposition, [status(thm), theory('equality')], [c_30, c_215])).
% 2.36/1.38  tff(c_228, plain, (![A_108, F_109]: (k2_xboole_0(k1_tarski(A_108), k1_tarski(F_109))=k2_tarski(A_108, F_109))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_224])).
% 2.36/1.38  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.38  tff(c_234, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_46])).
% 2.36/1.38  tff(c_63, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.38  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.38  tff(c_69, plain, (![B_55, A_54]: (r2_hidden(B_55, k2_tarski(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_6])).
% 2.36/1.38  tff(c_255, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_69])).
% 2.36/1.38  tff(c_119, plain, (![E_70, C_71, B_72, A_73]: (E_70=C_71 | E_70=B_72 | E_70=A_73 | ~r2_hidden(E_70, k1_enumset1(A_73, B_72, C_71)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.38  tff(c_147, plain, (![E_79, B_80, A_81]: (E_79=B_80 | E_79=A_81 | E_79=A_81 | ~r2_hidden(E_79, k2_tarski(A_81, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_119])).
% 2.36/1.38  tff(c_156, plain, (![E_79, A_16]: (E_79=A_16 | E_79=A_16 | E_79=A_16 | ~r2_hidden(E_79, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_147])).
% 2.36/1.38  tff(c_272, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_255, c_156])).
% 2.36/1.38  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_44, c_272])).
% 2.36/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.38  
% 2.36/1.38  Inference rules
% 2.36/1.38  ----------------------
% 2.36/1.38  #Ref     : 0
% 2.36/1.38  #Sup     : 54
% 2.36/1.38  #Fact    : 0
% 2.36/1.38  #Define  : 0
% 2.36/1.38  #Split   : 0
% 2.36/1.38  #Chain   : 0
% 2.36/1.38  #Close   : 0
% 2.36/1.38  
% 2.36/1.38  Ordering : KBO
% 2.36/1.38  
% 2.36/1.38  Simplification rules
% 2.36/1.38  ----------------------
% 2.36/1.38  #Subsume      : 0
% 2.36/1.38  #Demod        : 8
% 2.36/1.38  #Tautology    : 39
% 2.36/1.38  #SimpNegUnit  : 1
% 2.36/1.38  #BackRed      : 0
% 2.36/1.38  
% 2.36/1.38  #Partial instantiations: 0
% 2.36/1.38  #Strategies tried      : 1
% 2.36/1.38  
% 2.36/1.38  Timing (in seconds)
% 2.36/1.38  ----------------------
% 2.36/1.38  Preprocessing        : 0.37
% 2.36/1.38  Parsing              : 0.19
% 2.36/1.38  CNF conversion       : 0.03
% 2.36/1.38  Main loop            : 0.22
% 2.36/1.38  Inferencing          : 0.09
% 2.36/1.38  Reduction            : 0.07
% 2.36/1.38  Demodulation         : 0.05
% 2.36/1.38  BG Simplification    : 0.02
% 2.36/1.38  Subsumption          : 0.03
% 2.36/1.38  Abstraction          : 0.01
% 2.36/1.38  MUC search           : 0.00
% 2.36/1.38  Cooper               : 0.00
% 2.36/1.38  Total                : 0.62
% 2.36/1.38  Index Insertion      : 0.00
% 2.36/1.38  Index Deletion       : 0.00
% 2.36/1.38  Index Matching       : 0.00
% 2.36/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
