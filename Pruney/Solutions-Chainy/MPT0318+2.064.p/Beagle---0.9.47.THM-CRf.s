%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:10 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 124 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 ( 177 expanded)
%              Number of equality atoms :   38 ( 159 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_64,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_28,plain,(
    ! [B_37] : k2_zfmisc_1(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,
    ( k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_116,plain,(
    ! [B_55,A_56] :
      ( k1_xboole_0 = B_55
      | k1_xboole_0 = A_56
      | k2_zfmisc_1(A_56,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_116])).

tff(c_128,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_119])).

tff(c_32,plain,(
    ! [A_38] : k3_tarski(k1_tarski(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_138,plain,(
    k3_tarski(k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_32])).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_30])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_6,C_53] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_114,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_159,plain,(
    ! [C_53] : ~ r2_hidden(C_53,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_114])).

tff(c_162,plain,(
    ! [B_37] : k2_zfmisc_1('#skF_3',B_37) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_151,c_28])).

tff(c_157,plain,(
    k1_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_128])).

tff(c_195,plain,(
    ! [C_63,D_64] : r2_hidden(k4_tarski(C_63,D_64),k2_zfmisc_1(k1_tarski(C_63),k1_tarski(D_64))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_198,plain,(
    ! [D_64] : r2_hidden(k4_tarski('#skF_3',D_64),k2_zfmisc_1('#skF_3',k1_tarski(D_64))) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_195])).

tff(c_235,plain,(
    ! [D_64] : r2_hidden(k4_tarski('#skF_3',D_64),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_198])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_235])).

tff(c_237,plain,(
    k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_250,plain,(
    ! [B_73,A_74] :
      ( k1_xboole_0 = B_73
      | k1_xboole_0 = A_74
      | k2_zfmisc_1(A_74,B_73) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_253,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_250])).

tff(c_262,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_253])).

tff(c_238,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_276,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_238])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.27  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.27  
% 2.28/1.27  %Foreground sorts:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Background operators:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Foreground operators:
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.27  
% 2.28/1.28  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.28/1.28  tff(f_82, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.28/1.28  tff(f_66, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.28/1.28  tff(f_64, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.28/1.28  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.28/1.28  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.28/1.28  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.28/1.28  tff(f_72, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.28/1.28  tff(c_28, plain, (![B_37]: (k2_zfmisc_1(k1_xboole_0, B_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.28  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.28/1.28  tff(c_40, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.28/1.28  tff(c_104, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.28/1.28  tff(c_116, plain, (![B_55, A_56]: (k1_xboole_0=B_55 | k1_xboole_0=A_56 | k2_zfmisc_1(A_56, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.28  tff(c_119, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_104, c_116])).
% 2.28/1.28  tff(c_128, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_119])).
% 2.28/1.28  tff(c_32, plain, (![A_38]: (k3_tarski(k1_tarski(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.28  tff(c_138, plain, (k3_tarski(k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_128, c_32])).
% 2.28/1.28  tff(c_30, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.28  tff(c_151, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_30])).
% 2.28/1.28  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.28  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.28  tff(c_109, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.28  tff(c_112, plain, (![A_6, C_53]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_109])).
% 2.28/1.28  tff(c_114, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 2.28/1.28  tff(c_159, plain, (![C_53]: (~r2_hidden(C_53, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_114])).
% 2.28/1.28  tff(c_162, plain, (![B_37]: (k2_zfmisc_1('#skF_3', B_37)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_151, c_28])).
% 2.28/1.28  tff(c_157, plain, (k1_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_128])).
% 2.28/1.28  tff(c_195, plain, (![C_63, D_64]: (r2_hidden(k4_tarski(C_63, D_64), k2_zfmisc_1(k1_tarski(C_63), k1_tarski(D_64))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.28/1.28  tff(c_198, plain, (![D_64]: (r2_hidden(k4_tarski('#skF_3', D_64), k2_zfmisc_1('#skF_3', k1_tarski(D_64))))), inference(superposition, [status(thm), theory('equality')], [c_157, c_195])).
% 2.28/1.28  tff(c_235, plain, (![D_64]: (r2_hidden(k4_tarski('#skF_3', D_64), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_198])).
% 2.28/1.28  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_235])).
% 2.28/1.28  tff(c_237, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.28/1.28  tff(c_250, plain, (![B_73, A_74]: (k1_xboole_0=B_73 | k1_xboole_0=A_74 | k2_zfmisc_1(A_74, B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.28  tff(c_253, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_237, c_250])).
% 2.28/1.28  tff(c_262, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_253])).
% 2.28/1.28  tff(c_238, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.28/1.28  tff(c_276, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_262, c_238])).
% 2.28/1.28  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_276])).
% 2.28/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  Inference rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Ref     : 0
% 2.28/1.28  #Sup     : 57
% 2.28/1.28  #Fact    : 0
% 2.28/1.28  #Define  : 0
% 2.28/1.28  #Split   : 1
% 2.28/1.28  #Chain   : 0
% 2.28/1.28  #Close   : 0
% 2.28/1.28  
% 2.28/1.28  Ordering : KBO
% 2.28/1.28  
% 2.28/1.28  Simplification rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Subsume      : 1
% 2.28/1.28  #Demod        : 25
% 2.28/1.28  #Tautology    : 50
% 2.28/1.28  #SimpNegUnit  : 3
% 2.28/1.28  #BackRed      : 13
% 2.28/1.28  
% 2.28/1.28  #Partial instantiations: 0
% 2.28/1.28  #Strategies tried      : 1
% 2.28/1.28  
% 2.28/1.28  Timing (in seconds)
% 2.28/1.28  ----------------------
% 2.28/1.28  Preprocessing        : 0.32
% 2.28/1.28  Parsing              : 0.17
% 2.28/1.28  CNF conversion       : 0.02
% 2.28/1.28  Main loop            : 0.16
% 2.28/1.28  Inferencing          : 0.05
% 2.28/1.28  Reduction            : 0.05
% 2.28/1.28  Demodulation         : 0.04
% 2.28/1.28  BG Simplification    : 0.01
% 2.28/1.28  Subsumption          : 0.03
% 2.28/1.28  Abstraction          : 0.01
% 2.28/1.28  MUC search           : 0.00
% 2.28/1.28  Cooper               : 0.00
% 2.28/1.28  Total                : 0.51
% 2.28/1.28  Index Insertion      : 0.00
% 2.28/1.28  Index Deletion       : 0.00
% 2.28/1.28  Index Matching       : 0.00
% 2.28/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
