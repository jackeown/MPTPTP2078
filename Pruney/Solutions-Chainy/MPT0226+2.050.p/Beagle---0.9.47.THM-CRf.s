%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:43 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 (  78 expanded)
%              Number of equality atoms :   48 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_46,B_47,C_48,D_49] : k3_enumset1(A_46,A_46,B_47,C_48,D_49) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,(
    ! [A_50,B_51,E_54,C_52,D_53] : k4_enumset1(A_50,A_50,B_51,C_52,D_53,E_54) = k3_enumset1(A_50,B_51,C_52,D_53,E_54) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [B_56,E_59,C_57,A_55,F_60,D_58] : k5_enumset1(A_55,A_55,B_56,C_57,D_58,E_59,F_60) = k4_enumset1(A_55,B_56,C_57,D_58,E_59,F_60) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_399,plain,(
    ! [C_136,F_139,A_137,B_138,G_142,E_141,D_140] : k2_xboole_0(k3_enumset1(A_137,B_138,C_136,D_140,E_141),k2_tarski(F_139,G_142)) = k5_enumset1(A_137,B_138,C_136,D_140,E_141,F_139,G_142) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_408,plain,(
    ! [A_46,B_47,F_139,C_48,D_49,G_142] : k5_enumset1(A_46,A_46,B_47,C_48,D_49,F_139,G_142) = k2_xboole_0(k2_enumset1(A_46,B_47,C_48,D_49),k2_tarski(F_139,G_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_399])).

tff(c_415,plain,(
    ! [F_146,C_147,B_143,D_144,G_145,A_148] : k2_xboole_0(k2_enumset1(A_148,B_143,C_147,D_144),k2_tarski(F_146,G_145)) = k4_enumset1(A_148,B_143,C_147,D_144,F_146,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_408])).

tff(c_433,plain,(
    ! [F_146,G_145,C_45,A_43,B_44] : k4_enumset1(A_43,A_43,B_44,C_45,F_146,G_145) = k2_xboole_0(k1_enumset1(A_43,B_44,C_45),k2_tarski(F_146,G_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_415])).

tff(c_440,plain,(
    ! [F_149,B_152,G_153,C_150,A_151] : k2_xboole_0(k1_enumset1(A_151,B_152,C_150),k2_tarski(F_149,G_153)) = k3_enumset1(A_151,B_152,C_150,F_149,G_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_433])).

tff(c_455,plain,(
    ! [A_41,B_42,F_149,G_153] : k3_enumset1(A_41,A_41,B_42,F_149,G_153) = k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(F_149,G_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_440])).

tff(c_463,plain,(
    ! [A_158,B_159,F_160,G_161] : k2_xboole_0(k2_tarski(A_158,B_159),k2_tarski(F_160,G_161)) = k2_enumset1(A_158,B_159,F_160,G_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_455])).

tff(c_472,plain,(
    ! [A_40,F_160,G_161] : k2_xboole_0(k1_tarski(A_40),k2_tarski(F_160,G_161)) = k2_enumset1(A_40,A_40,F_160,G_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_463])).

tff(c_480,plain,(
    ! [A_162,F_163,G_164] : k2_xboole_0(k1_tarski(A_162),k2_tarski(F_163,G_164)) = k1_enumset1(A_162,F_163,G_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_472])).

tff(c_492,plain,(
    ! [A_165,A_166] : k2_xboole_0(k1_tarski(A_165),k1_tarski(A_166)) = k1_enumset1(A_165,A_166,A_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_480])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_120,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k4_xboole_0(B_89,A_88)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_120])).

tff(c_132,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_516,plain,(
    k1_enumset1('#skF_4','#skF_3','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_132])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_567,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_10])).

tff(c_297,plain,(
    ! [E_106,C_107,B_108,A_109] :
      ( E_106 = C_107
      | E_106 = B_108
      | E_106 = A_109
      | ~ r2_hidden(E_106,k1_enumset1(A_109,B_108,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_331,plain,(
    ! [E_115,B_116,A_117] :
      ( E_115 = B_116
      | E_115 = A_117
      | E_115 = A_117
      | ~ r2_hidden(E_115,k2_tarski(A_117,B_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_297])).

tff(c_340,plain,(
    ! [E_115,A_40] :
      ( E_115 = A_40
      | E_115 = A_40
      | E_115 = A_40
      | ~ r2_hidden(E_115,k1_tarski(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_331])).

tff(c_581,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_567,c_340])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.47  
% 2.83/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.47  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.47  
% 2.83/1.47  %Foreground sorts:
% 2.83/1.47  
% 2.83/1.47  
% 2.83/1.47  %Background operators:
% 2.83/1.47  
% 2.83/1.47  
% 2.83/1.47  %Foreground operators:
% 2.83/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.83/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.83/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.83/1.47  
% 2.83/1.49  tff(f_73, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.83/1.49  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.83/1.49  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.83/1.49  tff(f_62, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.83/1.49  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.83/1.49  tff(f_64, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.83/1.49  tff(f_66, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.83/1.49  tff(f_50, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.83/1.49  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.83/1.49  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.83/1.49  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.83/1.49  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.49  tff(c_40, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.49  tff(c_44, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.49  tff(c_46, plain, (![A_46, B_47, C_48, D_49]: (k3_enumset1(A_46, A_46, B_47, C_48, D_49)=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.49  tff(c_42, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.49  tff(c_48, plain, (![A_50, B_51, E_54, C_52, D_53]: (k4_enumset1(A_50, A_50, B_51, C_52, D_53, E_54)=k3_enumset1(A_50, B_51, C_52, D_53, E_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.49  tff(c_50, plain, (![B_56, E_59, C_57, A_55, F_60, D_58]: (k5_enumset1(A_55, A_55, B_56, C_57, D_58, E_59, F_60)=k4_enumset1(A_55, B_56, C_57, D_58, E_59, F_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.49  tff(c_399, plain, (![C_136, F_139, A_137, B_138, G_142, E_141, D_140]: (k2_xboole_0(k3_enumset1(A_137, B_138, C_136, D_140, E_141), k2_tarski(F_139, G_142))=k5_enumset1(A_137, B_138, C_136, D_140, E_141, F_139, G_142))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.49  tff(c_408, plain, (![A_46, B_47, F_139, C_48, D_49, G_142]: (k5_enumset1(A_46, A_46, B_47, C_48, D_49, F_139, G_142)=k2_xboole_0(k2_enumset1(A_46, B_47, C_48, D_49), k2_tarski(F_139, G_142)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_399])).
% 2.83/1.49  tff(c_415, plain, (![F_146, C_147, B_143, D_144, G_145, A_148]: (k2_xboole_0(k2_enumset1(A_148, B_143, C_147, D_144), k2_tarski(F_146, G_145))=k4_enumset1(A_148, B_143, C_147, D_144, F_146, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_408])).
% 2.83/1.49  tff(c_433, plain, (![F_146, G_145, C_45, A_43, B_44]: (k4_enumset1(A_43, A_43, B_44, C_45, F_146, G_145)=k2_xboole_0(k1_enumset1(A_43, B_44, C_45), k2_tarski(F_146, G_145)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_415])).
% 2.83/1.49  tff(c_440, plain, (![F_149, B_152, G_153, C_150, A_151]: (k2_xboole_0(k1_enumset1(A_151, B_152, C_150), k2_tarski(F_149, G_153))=k3_enumset1(A_151, B_152, C_150, F_149, G_153))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_433])).
% 2.83/1.49  tff(c_455, plain, (![A_41, B_42, F_149, G_153]: (k3_enumset1(A_41, A_41, B_42, F_149, G_153)=k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(F_149, G_153)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_440])).
% 2.83/1.49  tff(c_463, plain, (![A_158, B_159, F_160, G_161]: (k2_xboole_0(k2_tarski(A_158, B_159), k2_tarski(F_160, G_161))=k2_enumset1(A_158, B_159, F_160, G_161))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_455])).
% 2.83/1.49  tff(c_472, plain, (![A_40, F_160, G_161]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(F_160, G_161))=k2_enumset1(A_40, A_40, F_160, G_161))), inference(superposition, [status(thm), theory('equality')], [c_40, c_463])).
% 2.83/1.49  tff(c_480, plain, (![A_162, F_163, G_164]: (k2_xboole_0(k1_tarski(A_162), k2_tarski(F_163, G_164))=k1_enumset1(A_162, F_163, G_164))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_472])).
% 2.83/1.49  tff(c_492, plain, (![A_165, A_166]: (k2_xboole_0(k1_tarski(A_165), k1_tarski(A_166))=k1_enumset1(A_165, A_166, A_166))), inference(superposition, [status(thm), theory('equality')], [c_40, c_480])).
% 2.83/1.49  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.49  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.49  tff(c_120, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k4_xboole_0(B_89, A_88))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.49  tff(c_129, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_120])).
% 2.83/1.49  tff(c_132, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_129])).
% 2.83/1.49  tff(c_516, plain, (k1_enumset1('#skF_4', '#skF_3', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_492, c_132])).
% 2.83/1.49  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.49  tff(c_567, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_516, c_10])).
% 2.83/1.49  tff(c_297, plain, (![E_106, C_107, B_108, A_109]: (E_106=C_107 | E_106=B_108 | E_106=A_109 | ~r2_hidden(E_106, k1_enumset1(A_109, B_108, C_107)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.49  tff(c_331, plain, (![E_115, B_116, A_117]: (E_115=B_116 | E_115=A_117 | E_115=A_117 | ~r2_hidden(E_115, k2_tarski(A_117, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_297])).
% 2.83/1.49  tff(c_340, plain, (![E_115, A_40]: (E_115=A_40 | E_115=A_40 | E_115=A_40 | ~r2_hidden(E_115, k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_331])).
% 2.83/1.49  tff(c_581, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_567, c_340])).
% 2.83/1.49  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_581])).
% 2.83/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.49  
% 2.83/1.49  Inference rules
% 2.83/1.49  ----------------------
% 2.83/1.49  #Ref     : 0
% 2.83/1.49  #Sup     : 131
% 2.83/1.49  #Fact    : 0
% 2.83/1.49  #Define  : 0
% 2.83/1.49  #Split   : 0
% 2.83/1.49  #Chain   : 0
% 2.83/1.49  #Close   : 0
% 2.83/1.49  
% 2.83/1.49  Ordering : KBO
% 2.83/1.49  
% 2.83/1.49  Simplification rules
% 2.83/1.49  ----------------------
% 2.83/1.49  #Subsume      : 5
% 2.83/1.49  #Demod        : 26
% 2.83/1.49  #Tautology    : 83
% 2.83/1.49  #SimpNegUnit  : 1
% 2.83/1.49  #BackRed      : 0
% 2.83/1.49  
% 2.83/1.49  #Partial instantiations: 0
% 2.83/1.49  #Strategies tried      : 1
% 2.83/1.49  
% 2.83/1.49  Timing (in seconds)
% 2.83/1.49  ----------------------
% 2.83/1.49  Preprocessing        : 0.36
% 2.83/1.49  Parsing              : 0.19
% 2.83/1.49  CNF conversion       : 0.03
% 2.83/1.49  Main loop            : 0.33
% 2.83/1.49  Inferencing          : 0.13
% 2.83/1.49  Reduction            : 0.10
% 2.83/1.49  Demodulation         : 0.08
% 2.83/1.49  BG Simplification    : 0.02
% 2.83/1.49  Subsumption          : 0.05
% 2.83/1.49  Abstraction          : 0.02
% 2.83/1.49  MUC search           : 0.00
% 2.83/1.50  Cooper               : 0.00
% 2.83/1.50  Total                : 0.73
% 2.83/1.50  Index Insertion      : 0.00
% 2.83/1.50  Index Deletion       : 0.00
% 2.83/1.50  Index Matching       : 0.00
% 2.83/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
