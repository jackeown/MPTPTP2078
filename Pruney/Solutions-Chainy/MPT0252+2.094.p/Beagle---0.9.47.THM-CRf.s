%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:12 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   53 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  86 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    ! [A_68,B_69] : k1_enumset1(A_68,A_68,B_69) = k2_tarski(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    ! [B_69,A_68] : r2_hidden(B_69,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12])).

tff(c_50,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,k3_tarski(B_67))
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_585,plain,(
    ! [A_149,A_150,B_151] :
      ( r1_tarski(A_149,k2_xboole_0(A_150,B_151))
      | ~ r2_hidden(A_149,k2_tarski(A_150,B_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_76])).

tff(c_592,plain,(
    ! [B_69,A_68] : r1_tarski(B_69,k2_xboole_0(A_68,B_69)) ),
    inference(resolution,[status(thm)],[c_89,c_585])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_113,plain,(
    ! [A_80,B_81] :
      ( r2_xboole_0(A_80,B_81)
      | B_81 = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [B_82,A_83] :
      ( ~ r1_tarski(B_82,A_83)
      | B_82 = A_83
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_113,c_8])).

tff(c_134,plain,
    ( k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_128])).

tff(c_144,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_144])).

tff(c_597,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_14,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_48,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,k3_tarski(B_44))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_107,plain,(
    ! [A_77,C_78,B_79] :
      ( r2_hidden(A_77,C_78)
      | ~ r1_tarski(k2_tarski(A_77,B_79),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_840,plain,(
    ! [A_181,B_182,B_183] :
      ( r2_hidden(A_181,k3_tarski(B_182))
      | ~ r2_hidden(k2_tarski(A_181,B_183),B_182) ) ),
    inference(resolution,[status(thm)],[c_48,c_107])).

tff(c_856,plain,(
    ! [A_181,B_183,B_69] : r2_hidden(A_181,k3_tarski(k2_tarski(k2_tarski(A_181,B_183),B_69))) ),
    inference(resolution,[status(thm)],[c_86,c_840])).

tff(c_889,plain,(
    ! [A_187,B_188,B_189] : r2_hidden(A_187,k2_xboole_0(k2_tarski(A_187,B_188),B_189)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_856])).

tff(c_900,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_889])).

tff(c_904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.51  
% 2.93/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.51  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.93/1.51  
% 2.93/1.51  %Foreground sorts:
% 2.93/1.51  
% 2.93/1.51  
% 2.93/1.51  %Background operators:
% 2.93/1.51  
% 2.93/1.51  
% 2.93/1.51  %Foreground operators:
% 2.93/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.93/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.51  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.93/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.93/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.93/1.51  
% 3.10/1.53  tff(f_83, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.10/1.53  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.10/1.53  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.10/1.53  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.10/1.53  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.10/1.53  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.10/1.53  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.10/1.53  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.10/1.53  tff(c_58, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.53  tff(c_80, plain, (![A_68, B_69]: (k1_enumset1(A_68, A_68, B_69)=k2_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.10/1.53  tff(c_12, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.53  tff(c_89, plain, (![B_69, A_68]: (r2_hidden(B_69, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_12])).
% 3.10/1.53  tff(c_50, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.10/1.53  tff(c_76, plain, (![A_66, B_67]: (r1_tarski(A_66, k3_tarski(B_67)) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.53  tff(c_585, plain, (![A_149, A_150, B_151]: (r1_tarski(A_149, k2_xboole_0(A_150, B_151)) | ~r2_hidden(A_149, k2_tarski(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_76])).
% 3.10/1.53  tff(c_592, plain, (![B_69, A_68]: (r1_tarski(B_69, k2_xboole_0(A_68, B_69)))), inference(resolution, [status(thm)], [c_89, c_585])).
% 3.10/1.53  tff(c_60, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.53  tff(c_113, plain, (![A_80, B_81]: (r2_xboole_0(A_80, B_81) | B_81=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.53  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.53  tff(c_128, plain, (![B_82, A_83]: (~r1_tarski(B_82, A_83) | B_82=A_83 | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_113, c_8])).
% 3.10/1.53  tff(c_134, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_128])).
% 3.10/1.53  tff(c_144, plain, (~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_134])).
% 3.10/1.53  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_592, c_144])).
% 3.10/1.53  tff(c_597, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_134])).
% 3.10/1.53  tff(c_14, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.53  tff(c_86, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_14])).
% 3.10/1.53  tff(c_48, plain, (![A_43, B_44]: (r1_tarski(A_43, k3_tarski(B_44)) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.53  tff(c_107, plain, (![A_77, C_78, B_79]: (r2_hidden(A_77, C_78) | ~r1_tarski(k2_tarski(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.10/1.53  tff(c_840, plain, (![A_181, B_182, B_183]: (r2_hidden(A_181, k3_tarski(B_182)) | ~r2_hidden(k2_tarski(A_181, B_183), B_182))), inference(resolution, [status(thm)], [c_48, c_107])).
% 3.10/1.53  tff(c_856, plain, (![A_181, B_183, B_69]: (r2_hidden(A_181, k3_tarski(k2_tarski(k2_tarski(A_181, B_183), B_69))))), inference(resolution, [status(thm)], [c_86, c_840])).
% 3.10/1.53  tff(c_889, plain, (![A_187, B_188, B_189]: (r2_hidden(A_187, k2_xboole_0(k2_tarski(A_187, B_188), B_189)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_856])).
% 3.10/1.53  tff(c_900, plain, (r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_597, c_889])).
% 3.10/1.53  tff(c_904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_900])).
% 3.10/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.53  
% 3.10/1.53  Inference rules
% 3.10/1.53  ----------------------
% 3.10/1.53  #Ref     : 0
% 3.10/1.53  #Sup     : 180
% 3.10/1.53  #Fact    : 0
% 3.10/1.53  #Define  : 0
% 3.10/1.53  #Split   : 1
% 3.10/1.53  #Chain   : 0
% 3.10/1.53  #Close   : 0
% 3.10/1.53  
% 3.10/1.53  Ordering : KBO
% 3.10/1.53  
% 3.10/1.53  Simplification rules
% 3.10/1.53  ----------------------
% 3.10/1.53  #Subsume      : 2
% 3.10/1.53  #Demod        : 58
% 3.10/1.53  #Tautology    : 101
% 3.10/1.53  #SimpNegUnit  : 1
% 3.10/1.53  #BackRed      : 2
% 3.10/1.53  
% 3.10/1.53  #Partial instantiations: 0
% 3.10/1.53  #Strategies tried      : 1
% 3.10/1.53  
% 3.10/1.53  Timing (in seconds)
% 3.10/1.53  ----------------------
% 3.10/1.53  Preprocessing        : 0.35
% 3.10/1.53  Parsing              : 0.18
% 3.10/1.53  CNF conversion       : 0.03
% 3.10/1.53  Main loop            : 0.35
% 3.10/1.53  Inferencing          : 0.13
% 3.10/1.53  Reduction            : 0.11
% 3.10/1.53  Demodulation         : 0.08
% 3.10/1.53  BG Simplification    : 0.02
% 3.10/1.53  Subsumption          : 0.07
% 3.10/1.53  Abstraction          : 0.02
% 3.10/1.53  MUC search           : 0.00
% 3.10/1.53  Cooper               : 0.00
% 3.10/1.53  Total                : 0.74
% 3.10/1.53  Index Insertion      : 0.00
% 3.10/1.53  Index Deletion       : 0.00
% 3.10/1.53  Index Matching       : 0.00
% 3.10/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
