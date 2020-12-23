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
% DateTime   : Thu Dec  3 09:54:04 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 126 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 223 expanded)
%              Number of equality atoms :   47 ( 189 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,k1_tarski(B_15)) = A_14
      | r2_hidden(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_105,plain,(
    ! [B_31,A_32] :
      ( k1_xboole_0 = B_31
      | k1_xboole_0 = A_32
      | k2_zfmisc_1(A_32,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_105])).

tff(c_117,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_108])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(A_34,C_35)
      | k4_xboole_0(k2_tarski(A_34,B_36),C_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_183,plain,(
    ! [A_39,C_40] :
      ( r2_hidden(A_39,C_40)
      | k4_xboole_0(k1_tarski(A_39),C_40) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_191,plain,(
    ! [C_41] :
      ( r2_hidden('#skF_4',C_41)
      | k4_xboole_0(k1_xboole_0,C_41) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_183])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,(
    ! [A_42] :
      ( A_42 = '#skF_4'
      | k4_xboole_0(k1_xboole_0,k1_tarski(A_42)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_215,plain,(
    ! [B_43] :
      ( B_43 = '#skF_4'
      | r2_hidden(B_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_206])).

tff(c_133,plain,(
    ! [C_5] :
      ( C_5 = '#skF_4'
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_2])).

tff(c_224,plain,(
    ! [B_43] : B_43 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_215,c_133])).

tff(c_225,plain,(
    ! [B_44] : B_44 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_215,c_133])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_4])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( ~ r2_hidden(B_15,A_14)
      | k4_xboole_0(A_14,k1_tarski(B_15)) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_154,plain,(
    ! [A_37] :
      ( ~ r2_hidden('#skF_4',A_37)
      | k4_xboole_0(A_37,k1_xboole_0) != A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_26])).

tff(c_162,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_154])).

tff(c_235,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_162])).

tff(c_287,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_235])).

tff(c_288,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_294,plain,(
    ! [B_473,A_474] :
      ( k1_xboole_0 = B_473
      | k1_xboole_0 = A_474
      | k2_zfmisc_1(A_474,B_473) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_297,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_294])).

tff(c_306,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_297])).

tff(c_289,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_311,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_289])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.00/1.22  
% 2.00/1.22  %Foreground sorts:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Background operators:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Foreground operators:
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.22  
% 2.00/1.23  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.00/1.23  tff(f_65, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.00/1.23  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.00/1.23  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.00/1.23  tff(f_55, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.00/1.23  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.00/1.23  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.23  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.23  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k1_tarski(B_15))=A_14 | r2_hidden(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.00/1.23  tff(c_36, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.23  tff(c_100, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.00/1.23  tff(c_105, plain, (![B_31, A_32]: (k1_xboole_0=B_31 | k1_xboole_0=A_32 | k2_zfmisc_1(A_32, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.23  tff(c_108, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_105])).
% 2.00/1.23  tff(c_117, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_38, c_108])).
% 2.00/1.23  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.23  tff(c_146, plain, (![A_34, C_35, B_36]: (r2_hidden(A_34, C_35) | k4_xboole_0(k2_tarski(A_34, B_36), C_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.23  tff(c_183, plain, (![A_39, C_40]: (r2_hidden(A_39, C_40) | k4_xboole_0(k1_tarski(A_39), C_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 2.00/1.23  tff(c_191, plain, (![C_41]: (r2_hidden('#skF_4', C_41) | k4_xboole_0(k1_xboole_0, C_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_183])).
% 2.00/1.23  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.23  tff(c_206, plain, (![A_42]: (A_42='#skF_4' | k4_xboole_0(k1_xboole_0, k1_tarski(A_42))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_191, c_2])).
% 2.00/1.23  tff(c_215, plain, (![B_43]: (B_43='#skF_4' | r2_hidden(B_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_206])).
% 2.00/1.23  tff(c_133, plain, (![C_5]: (C_5='#skF_4' | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117, c_2])).
% 2.00/1.23  tff(c_224, plain, (![B_43]: (B_43='#skF_4')), inference(resolution, [status(thm)], [c_215, c_133])).
% 2.00/1.23  tff(c_225, plain, (![B_44]: (B_44='#skF_4')), inference(resolution, [status(thm)], [c_215, c_133])).
% 2.00/1.23  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.23  tff(c_136, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_4])).
% 2.00/1.23  tff(c_26, plain, (![B_15, A_14]: (~r2_hidden(B_15, A_14) | k4_xboole_0(A_14, k1_tarski(B_15))!=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.00/1.23  tff(c_154, plain, (![A_37]: (~r2_hidden('#skF_4', A_37) | k4_xboole_0(A_37, k1_xboole_0)!=A_37)), inference(superposition, [status(thm), theory('equality')], [c_117, c_26])).
% 2.00/1.23  tff(c_162, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_154])).
% 2.00/1.23  tff(c_235, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_225, c_162])).
% 2.00/1.23  tff(c_287, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_224, c_235])).
% 2.00/1.23  tff(c_288, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.00/1.23  tff(c_294, plain, (![B_473, A_474]: (k1_xboole_0=B_473 | k1_xboole_0=A_474 | k2_zfmisc_1(A_474, B_473)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.23  tff(c_297, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_288, c_294])).
% 2.00/1.23  tff(c_306, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_38, c_297])).
% 2.00/1.23  tff(c_289, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.00/1.23  tff(c_311, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_306, c_289])).
% 2.00/1.23  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_311])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 75
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 1
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 14
% 2.00/1.23  #Demod        : 7
% 2.00/1.23  #Tautology    : 30
% 2.00/1.23  #SimpNegUnit  : 3
% 2.00/1.23  #BackRed      : 3
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.29
% 2.00/1.23  Parsing              : 0.15
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.18
% 2.00/1.23  Inferencing          : 0.08
% 2.00/1.23  Reduction            : 0.05
% 2.00/1.23  Demodulation         : 0.03
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.03
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.49
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
