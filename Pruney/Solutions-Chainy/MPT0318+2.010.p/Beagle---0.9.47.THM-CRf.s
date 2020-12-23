%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 108 expanded)
%              Number of equality atoms :   36 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_58,plain,(
    ! [B_41] : k2_zfmisc_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_122,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_138,plain,(
    ! [B_62,A_63] :
      ( k1_xboole_0 = B_62
      | k1_xboole_0 = A_63
      | k2_zfmisc_1(A_63,B_62) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_141,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_138])).

tff(c_150,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_141])).

tff(c_40,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [A_57,B_58] : r2_hidden(A_57,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_20])).

tff(c_130,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_127])).

tff(c_160,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_130])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_177,plain,(
    ! [A_70,C_71,B_72] :
      ( ~ r2_hidden(A_70,C_71)
      | ~ r2_hidden(A_70,B_72)
      | ~ r2_hidden(A_70,k5_xboole_0(B_72,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_73,A_74] :
      ( ~ r2_hidden(A_73,A_74)
      | ~ r2_hidden(A_73,A_74)
      | ~ r2_hidden(A_73,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_160,c_185])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_189])).

tff(c_207,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_217,plain,(
    ! [B_77,A_78] :
      ( k1_xboole_0 = B_77
      | k1_xboole_0 = A_78
      | k2_zfmisc_1(A_78,B_77) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_220,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_217])).

tff(c_229,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_220])).

tff(c_208,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_234,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_208])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.22  
% 2.12/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.22  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.22  
% 2.12/1.22  %Foreground sorts:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Background operators:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Foreground operators:
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.12/1.22  
% 2.15/1.23  tff(f_69, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.15/1.23  tff(f_79, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.15/1.23  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.23  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.23  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.15/1.23  tff(f_34, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.15/1.23  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.15/1.23  tff(c_58, plain, (![B_41]: (k2_zfmisc_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.23  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.23  tff(c_60, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.23  tff(c_122, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 2.15/1.23  tff(c_138, plain, (![B_62, A_63]: (k1_xboole_0=B_62 | k1_xboole_0=A_63 | k2_zfmisc_1(A_63, B_62)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.23  tff(c_141, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122, c_138])).
% 2.15/1.23  tff(c_150, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_141])).
% 2.15/1.23  tff(c_40, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.23  tff(c_104, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.23  tff(c_20, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.23  tff(c_127, plain, (![A_57, B_58]: (r2_hidden(A_57, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_20])).
% 2.15/1.23  tff(c_130, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_127])).
% 2.15/1.23  tff(c_160, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_150, c_130])).
% 2.15/1.23  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.23  tff(c_177, plain, (![A_70, C_71, B_72]: (~r2_hidden(A_70, C_71) | ~r2_hidden(A_70, B_72) | ~r2_hidden(A_70, k5_xboole_0(B_72, C_71)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.23  tff(c_185, plain, (![A_73, A_74]: (~r2_hidden(A_73, A_74) | ~r2_hidden(A_73, A_74) | ~r2_hidden(A_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_177])).
% 2.15/1.23  tff(c_189, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_185])).
% 2.15/1.23  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_189])).
% 2.15/1.23  tff(c_207, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 2.15/1.23  tff(c_217, plain, (![B_77, A_78]: (k1_xboole_0=B_77 | k1_xboole_0=A_78 | k2_zfmisc_1(A_78, B_77)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.23  tff(c_220, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_207, c_217])).
% 2.15/1.23  tff(c_229, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_220])).
% 2.15/1.23  tff(c_208, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 2.15/1.23  tff(c_234, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_229, c_208])).
% 2.15/1.23  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_234])).
% 2.15/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  Inference rules
% 2.15/1.23  ----------------------
% 2.15/1.23  #Ref     : 0
% 2.15/1.23  #Sup     : 44
% 2.15/1.23  #Fact    : 0
% 2.15/1.23  #Define  : 0
% 2.15/1.23  #Split   : 1
% 2.15/1.23  #Chain   : 0
% 2.15/1.23  #Close   : 0
% 2.15/1.23  
% 2.15/1.23  Ordering : KBO
% 2.15/1.23  
% 2.15/1.23  Simplification rules
% 2.15/1.23  ----------------------
% 2.15/1.23  #Subsume      : 0
% 2.15/1.23  #Demod        : 8
% 2.15/1.23  #Tautology    : 31
% 2.15/1.23  #SimpNegUnit  : 2
% 2.15/1.23  #BackRed      : 3
% 2.15/1.23  
% 2.15/1.23  #Partial instantiations: 0
% 2.15/1.23  #Strategies tried      : 1
% 2.15/1.24  
% 2.15/1.24  Timing (in seconds)
% 2.15/1.24  ----------------------
% 2.15/1.24  Preprocessing        : 0.32
% 2.15/1.24  Parsing              : 0.16
% 2.15/1.24  CNF conversion       : 0.02
% 2.15/1.24  Main loop            : 0.16
% 2.15/1.24  Inferencing          : 0.05
% 2.15/1.24  Reduction            : 0.06
% 2.15/1.24  Demodulation         : 0.04
% 2.15/1.24  BG Simplification    : 0.01
% 2.15/1.24  Subsumption          : 0.03
% 2.15/1.24  Abstraction          : 0.01
% 2.15/1.24  MUC search           : 0.00
% 2.15/1.24  Cooper               : 0.00
% 2.15/1.24  Total                : 0.51
% 2.15/1.24  Index Insertion      : 0.00
% 2.15/1.24  Index Deletion       : 0.00
% 2.15/1.24  Index Matching       : 0.00
% 2.15/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
