%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:37 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  86 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_33,B_34] : r2_hidden(A_33,k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_32,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    ! [B_34,A_33] : r2_hidden(B_34,k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_32])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_90])).

tff(c_114,plain,(
    ! [D_47,B_48,A_49] :
      ( ~ r2_hidden(D_47,B_48)
      | ~ r2_hidden(D_47,k4_xboole_0(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [D_52,B_53] :
      ( ~ r2_hidden(D_52,B_53)
      | ~ r2_hidden(D_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_114])).

tff(c_130,plain,(
    ! [B_34] : ~ r2_hidden(B_34,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80,c_119])).

tff(c_62,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_101,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_90])).

tff(c_194,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,k4_xboole_0(A_65,B_66))
      | r2_hidden(D_64,B_66)
      | ~ r2_hidden(D_64,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,k1_xboole_0)
      | r2_hidden(D_64,k2_tarski('#skF_7','#skF_8'))
      | ~ r2_hidden(D_64,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_194])).

tff(c_209,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,k2_tarski('#skF_7','#skF_8'))
      | ~ r2_hidden(D_64,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_203])).

tff(c_54,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_217,plain,(
    ! [E_68,C_69,B_70,A_71] :
      ( E_68 = C_69
      | E_68 = B_70
      | E_68 = A_71
      | ~ r2_hidden(E_68,k1_enumset1(A_71,B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    ! [E_72,B_73,A_74] :
      ( E_72 = B_73
      | E_72 = A_74
      | E_72 = A_74
      | ~ r2_hidden(E_72,k2_tarski(A_74,B_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_217])).

tff(c_260,plain,(
    ! [D_78] :
      ( D_78 = '#skF_8'
      | D_78 = '#skF_7'
      | ~ r2_hidden(D_78,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_209,c_236])).

tff(c_268,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_74,c_260])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:00:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.24  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.08/1.24  
% 2.08/1.24  %Foreground sorts:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Background operators:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Foreground operators:
% 2.08/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.08/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.08/1.24  tff('#skF_8', type, '#skF_8': $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.08/1.24  
% 2.14/1.25  tff(f_74, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.14/1.25  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.14/1.25  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.14/1.25  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.25  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.14/1.25  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.14/1.25  tff(c_60, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_58, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_68, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.25  tff(c_34, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.25  tff(c_74, plain, (![A_33, B_34]: (r2_hidden(A_33, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_34])).
% 2.14/1.25  tff(c_32, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.25  tff(c_80, plain, (![B_34, A_33]: (r2_hidden(B_34, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_32])).
% 2.14/1.25  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.25  tff(c_90, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.25  tff(c_102, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_90])).
% 2.14/1.25  tff(c_114, plain, (![D_47, B_48, A_49]: (~r2_hidden(D_47, B_48) | ~r2_hidden(D_47, k4_xboole_0(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.25  tff(c_119, plain, (![D_52, B_53]: (~r2_hidden(D_52, B_53) | ~r2_hidden(D_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_102, c_114])).
% 2.14/1.25  tff(c_130, plain, (![B_34]: (~r2_hidden(B_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_119])).
% 2.14/1.25  tff(c_62, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_101, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_90])).
% 2.14/1.25  tff(c_194, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, k4_xboole_0(A_65, B_66)) | r2_hidden(D_64, B_66) | ~r2_hidden(D_64, A_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.25  tff(c_203, plain, (![D_64]: (r2_hidden(D_64, k1_xboole_0) | r2_hidden(D_64, k2_tarski('#skF_7', '#skF_8')) | ~r2_hidden(D_64, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_101, c_194])).
% 2.14/1.25  tff(c_209, plain, (![D_64]: (r2_hidden(D_64, k2_tarski('#skF_7', '#skF_8')) | ~r2_hidden(D_64, k2_tarski('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_130, c_203])).
% 2.14/1.25  tff(c_54, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.25  tff(c_217, plain, (![E_68, C_69, B_70, A_71]: (E_68=C_69 | E_68=B_70 | E_68=A_71 | ~r2_hidden(E_68, k1_enumset1(A_71, B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.25  tff(c_236, plain, (![E_72, B_73, A_74]: (E_72=B_73 | E_72=A_74 | E_72=A_74 | ~r2_hidden(E_72, k2_tarski(A_74, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_217])).
% 2.14/1.25  tff(c_260, plain, (![D_78]: (D_78='#skF_8' | D_78='#skF_7' | ~r2_hidden(D_78, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_209, c_236])).
% 2.14/1.25  tff(c_268, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_74, c_260])).
% 2.14/1.25  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_268])).
% 2.14/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  Inference rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Ref     : 0
% 2.14/1.25  #Sup     : 47
% 2.14/1.25  #Fact    : 0
% 2.14/1.25  #Define  : 0
% 2.14/1.25  #Split   : 1
% 2.14/1.25  #Chain   : 0
% 2.14/1.25  #Close   : 0
% 2.14/1.25  
% 2.14/1.25  Ordering : KBO
% 2.14/1.25  
% 2.14/1.25  Simplification rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Subsume      : 8
% 2.14/1.25  #Demod        : 5
% 2.14/1.25  #Tautology    : 22
% 2.14/1.25  #SimpNegUnit  : 3
% 2.14/1.25  #BackRed      : 0
% 2.14/1.25  
% 2.14/1.25  #Partial instantiations: 0
% 2.14/1.25  #Strategies tried      : 1
% 2.14/1.25  
% 2.14/1.25  Timing (in seconds)
% 2.14/1.25  ----------------------
% 2.14/1.25  Preprocessing        : 0.30
% 2.14/1.25  Parsing              : 0.15
% 2.14/1.26  CNF conversion       : 0.02
% 2.14/1.26  Main loop            : 0.19
% 2.14/1.26  Inferencing          : 0.06
% 2.14/1.26  Reduction            : 0.06
% 2.14/1.26  Demodulation         : 0.04
% 2.14/1.26  BG Simplification    : 0.02
% 2.14/1.26  Subsumption          : 0.04
% 2.14/1.26  Abstraction          : 0.01
% 2.14/1.26  MUC search           : 0.00
% 2.14/1.26  Cooper               : 0.00
% 2.14/1.26  Total                : 0.52
% 2.14/1.26  Index Insertion      : 0.00
% 2.14/1.26  Index Deletion       : 0.00
% 2.14/1.26  Index Matching       : 0.00
% 2.14/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
