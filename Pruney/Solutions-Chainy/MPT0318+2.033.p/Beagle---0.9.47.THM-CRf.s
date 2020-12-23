%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:06 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 141 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 257 expanded)
%              Number of equality atoms :   53 ( 218 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_30,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,k1_tarski(B_16)) = A_15
      | r2_hidden(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_114,plain,(
    ! [B_34,A_35] :
      ( k1_xboole_0 = B_34
      | k1_xboole_0 = A_35
      | k2_zfmisc_1(A_35,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_114])).

tff(c_126,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_117])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_193,plain,(
    ! [A_43,C_44,B_45] :
      ( r2_hidden(A_43,C_44)
      | k4_xboole_0(k2_tarski(A_43,B_45),C_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [A_46,C_47] :
      ( r2_hidden(A_46,C_47)
      | k4_xboole_0(k1_tarski(A_46),C_47) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_193])).

tff(c_204,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4',C_47)
      | k4_xboole_0(k1_xboole_0,C_47) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_201])).

tff(c_209,plain,(
    ! [D_48,B_49,A_50] :
      ( D_48 = B_49
      | D_48 = A_50
      | ~ r2_hidden(D_48,k2_tarski(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_238,plain,(
    ! [D_52,A_53] :
      ( D_52 = A_53
      | D_52 = A_53
      | ~ r2_hidden(D_52,k1_tarski(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_209])).

tff(c_276,plain,(
    ! [A_55] :
      ( A_55 = '#skF_4'
      | k4_xboole_0(k1_xboole_0,k1_tarski(A_55)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_204,c_238])).

tff(c_285,plain,(
    ! [B_56] :
      ( B_56 = '#skF_4'
      | r2_hidden(B_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_276])).

tff(c_249,plain,(
    ! [D_52] :
      ( D_52 = '#skF_4'
      | D_52 = '#skF_4'
      | ~ r2_hidden(D_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_238])).

tff(c_293,plain,(
    ! [B_56] : B_56 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_285,c_249])).

tff(c_295,plain,(
    ! [B_57] : B_57 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_285,c_249])).

tff(c_69,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_4])).

tff(c_142,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_75])).

tff(c_32,plain,(
    ! [B_16,A_15] :
      ( ~ r2_hidden(B_16,A_15)
      | k4_xboole_0(A_15,k1_tarski(B_16)) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_156,plain,(
    ! [A_40] :
      ( ~ r2_hidden('#skF_4',A_40)
      | k4_xboole_0(A_40,k1_xboole_0) != A_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_32])).

tff(c_176,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_156])).

tff(c_327,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_176])).

tff(c_368,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_327])).

tff(c_369,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_384,plain,(
    ! [B_631,A_632] :
      ( k1_xboole_0 = B_631
      | k1_xboole_0 = A_632
      | k2_zfmisc_1(A_632,B_631) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_387,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_384])).

tff(c_396,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_387])).

tff(c_370,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_401,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_370])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:40:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.35  
% 2.19/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.36  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.19/1.36  
% 2.19/1.36  %Foreground sorts:
% 2.19/1.36  
% 2.19/1.36  
% 2.19/1.36  %Background operators:
% 2.19/1.36  
% 2.19/1.36  
% 2.19/1.36  %Foreground operators:
% 2.19/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.36  
% 2.19/1.37  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.19/1.37  tff(f_67, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.19/1.37  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.19/1.37  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.37  tff(f_57, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.19/1.37  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.19/1.37  tff(c_30, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.37  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.37  tff(c_34, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k1_tarski(B_16))=A_15 | r2_hidden(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.37  tff(c_42, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.37  tff(c_95, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.19/1.37  tff(c_114, plain, (![B_34, A_35]: (k1_xboole_0=B_34 | k1_xboole_0=A_35 | k2_zfmisc_1(A_35, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.37  tff(c_117, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_114])).
% 2.19/1.37  tff(c_126, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_117])).
% 2.19/1.37  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.37  tff(c_193, plain, (![A_43, C_44, B_45]: (r2_hidden(A_43, C_44) | k4_xboole_0(k2_tarski(A_43, B_45), C_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.37  tff(c_201, plain, (![A_46, C_47]: (r2_hidden(A_46, C_47) | k4_xboole_0(k1_tarski(A_46), C_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_193])).
% 2.19/1.37  tff(c_204, plain, (![C_47]: (r2_hidden('#skF_4', C_47) | k4_xboole_0(k1_xboole_0, C_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_126, c_201])).
% 2.19/1.37  tff(c_209, plain, (![D_48, B_49, A_50]: (D_48=B_49 | D_48=A_50 | ~r2_hidden(D_48, k2_tarski(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.37  tff(c_238, plain, (![D_52, A_53]: (D_52=A_53 | D_52=A_53 | ~r2_hidden(D_52, k1_tarski(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_209])).
% 2.19/1.37  tff(c_276, plain, (![A_55]: (A_55='#skF_4' | k4_xboole_0(k1_xboole_0, k1_tarski(A_55))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_238])).
% 2.19/1.37  tff(c_285, plain, (![B_56]: (B_56='#skF_4' | r2_hidden(B_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_276])).
% 2.19/1.37  tff(c_249, plain, (![D_52]: (D_52='#skF_4' | D_52='#skF_4' | ~r2_hidden(D_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_126, c_238])).
% 2.19/1.37  tff(c_293, plain, (![B_56]: (B_56='#skF_4')), inference(resolution, [status(thm)], [c_285, c_249])).
% 2.19/1.37  tff(c_295, plain, (![B_57]: (B_57='#skF_4')), inference(resolution, [status(thm)], [c_285, c_249])).
% 2.19/1.37  tff(c_69, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.37  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.37  tff(c_75, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_4])).
% 2.19/1.37  tff(c_142, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_126, c_75])).
% 2.19/1.37  tff(c_32, plain, (![B_16, A_15]: (~r2_hidden(B_16, A_15) | k4_xboole_0(A_15, k1_tarski(B_16))!=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.37  tff(c_156, plain, (![A_40]: (~r2_hidden('#skF_4', A_40) | k4_xboole_0(A_40, k1_xboole_0)!=A_40)), inference(superposition, [status(thm), theory('equality')], [c_126, c_32])).
% 2.19/1.37  tff(c_176, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_156])).
% 2.19/1.37  tff(c_327, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_295, c_176])).
% 2.19/1.37  tff(c_368, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_293, c_327])).
% 2.19/1.37  tff(c_369, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.19/1.37  tff(c_384, plain, (![B_631, A_632]: (k1_xboole_0=B_631 | k1_xboole_0=A_632 | k2_zfmisc_1(A_632, B_631)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.37  tff(c_387, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_369, c_384])).
% 2.19/1.37  tff(c_396, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_387])).
% 2.19/1.37  tff(c_370, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.19/1.37  tff(c_401, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_396, c_370])).
% 2.19/1.37  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_401])).
% 2.19/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.37  
% 2.19/1.37  Inference rules
% 2.19/1.37  ----------------------
% 2.19/1.37  #Ref     : 0
% 2.19/1.37  #Sup     : 99
% 2.19/1.37  #Fact    : 0
% 2.19/1.37  #Define  : 0
% 2.19/1.37  #Split   : 1
% 2.19/1.37  #Chain   : 0
% 2.19/1.37  #Close   : 0
% 2.19/1.37  
% 2.19/1.37  Ordering : KBO
% 2.19/1.37  
% 2.19/1.37  Simplification rules
% 2.19/1.37  ----------------------
% 2.19/1.37  #Subsume      : 16
% 2.19/1.37  #Demod        : 14
% 2.19/1.37  #Tautology    : 35
% 2.19/1.37  #SimpNegUnit  : 3
% 2.19/1.37  #BackRed      : 3
% 2.19/1.37  
% 2.19/1.37  #Partial instantiations: 0
% 2.19/1.37  #Strategies tried      : 1
% 2.19/1.37  
% 2.19/1.37  Timing (in seconds)
% 2.19/1.37  ----------------------
% 2.19/1.37  Preprocessing        : 0.32
% 2.19/1.37  Parsing              : 0.16
% 2.19/1.37  CNF conversion       : 0.02
% 2.19/1.37  Main loop            : 0.23
% 2.19/1.37  Inferencing          : 0.09
% 2.19/1.37  Reduction            : 0.06
% 2.19/1.37  Demodulation         : 0.05
% 2.19/1.37  BG Simplification    : 0.02
% 2.19/1.37  Subsumption          : 0.04
% 2.19/1.37  Abstraction          : 0.01
% 2.19/1.37  MUC search           : 0.00
% 2.19/1.37  Cooper               : 0.00
% 2.19/1.37  Total                : 0.57
% 2.19/1.37  Index Insertion      : 0.00
% 2.19/1.37  Index Deletion       : 0.00
% 2.19/1.37  Index Matching       : 0.00
% 2.19/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
