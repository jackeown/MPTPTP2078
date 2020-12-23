%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:04 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 121 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 166 expanded)
%              Number of equality atoms :   36 ( 131 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_63,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_40,plain,(
    ! [B_41] : k2_zfmisc_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_145,plain,(
    ! [B_60,A_61] :
      ( k1_xboole_0 = B_60
      | k1_xboole_0 = A_61
      | k2_zfmisc_1(A_61,B_60) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_145])).

tff(c_157,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_148])).

tff(c_46,plain,(
    ! [A_42] : k3_tarski(k1_tarski(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    k3_tarski(k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_46])).

tff(c_44,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_171,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_44])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_6])).

tff(c_177,plain,(
    k1_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_157])).

tff(c_42,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_129,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(C_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_58,C_59] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_58))
      | ~ r1_tarski(C_59,A_58) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_143,plain,(
    ! [C_59] :
      ( ~ v1_xboole_0(k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_144,plain,(
    ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_179,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_144])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_177,c_179])).

tff(c_240,plain,(
    ! [C_67] : ~ r1_tarski(C_67,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_245,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_240])).

tff(c_246,plain,(
    k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_317,plain,(
    ! [B_80,A_81] :
      ( k1_xboole_0 = B_80
      | k1_xboole_0 = A_81
      | k2_zfmisc_1(A_81,B_80) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_320,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_317])).

tff(c_329,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_320])).

tff(c_247,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_334,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_247])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.14/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.25  
% 2.14/1.26  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.14/1.26  tff(f_75, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.14/1.26  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.14/1.26  tff(f_65, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.14/1.26  tff(f_63, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.14/1.26  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.14/1.26  tff(f_62, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.14/1.26  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.26  tff(c_40, plain, (![B_41]: (k2_zfmisc_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.26  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.26  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.14/1.26  tff(c_48, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.26  tff(c_92, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.14/1.26  tff(c_145, plain, (![B_60, A_61]: (k1_xboole_0=B_60 | k1_xboole_0=A_61 | k2_zfmisc_1(A_61, B_60)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.26  tff(c_148, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_145])).
% 2.14/1.26  tff(c_157, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_148])).
% 2.14/1.26  tff(c_46, plain, (![A_42]: (k3_tarski(k1_tarski(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.26  tff(c_167, plain, (k3_tarski(k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_157, c_46])).
% 2.14/1.26  tff(c_44, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.26  tff(c_171, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_44])).
% 2.14/1.26  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.26  tff(c_183, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_6])).
% 2.14/1.26  tff(c_177, plain, (k1_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_157])).
% 2.14/1.26  tff(c_42, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.26  tff(c_129, plain, (![C_56, A_57]: (r2_hidden(C_56, k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.26  tff(c_141, plain, (![A_58, C_59]: (~v1_xboole_0(k1_zfmisc_1(A_58)) | ~r1_tarski(C_59, A_58))), inference(resolution, [status(thm)], [c_129, c_2])).
% 2.14/1.26  tff(c_143, plain, (![C_59]: (~v1_xboole_0(k1_tarski(k1_xboole_0)) | ~r1_tarski(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_141])).
% 2.14/1.26  tff(c_144, plain, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_143])).
% 2.14/1.26  tff(c_179, plain, (~v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_144])).
% 2.14/1.26  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_177, c_179])).
% 2.14/1.26  tff(c_240, plain, (![C_67]: (~r1_tarski(C_67, k1_xboole_0))), inference(splitRight, [status(thm)], [c_143])).
% 2.14/1.26  tff(c_245, plain, $false, inference(resolution, [status(thm)], [c_8, c_240])).
% 2.14/1.26  tff(c_246, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.14/1.26  tff(c_317, plain, (![B_80, A_81]: (k1_xboole_0=B_80 | k1_xboole_0=A_81 | k2_zfmisc_1(A_81, B_80)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.26  tff(c_320, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_246, c_317])).
% 2.14/1.26  tff(c_329, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_320])).
% 2.14/1.26  tff(c_247, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.14/1.26  tff(c_334, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_329, c_247])).
% 2.14/1.26  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_334])).
% 2.14/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  Inference rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Ref     : 0
% 2.14/1.26  #Sup     : 68
% 2.14/1.26  #Fact    : 0
% 2.14/1.26  #Define  : 0
% 2.14/1.26  #Split   : 3
% 2.14/1.26  #Chain   : 0
% 2.14/1.26  #Close   : 0
% 2.14/1.26  
% 2.14/1.26  Ordering : KBO
% 2.14/1.26  
% 2.14/1.26  Simplification rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Subsume      : 1
% 2.14/1.26  #Demod        : 25
% 2.14/1.26  #Tautology    : 52
% 2.14/1.26  #SimpNegUnit  : 4
% 2.14/1.26  #BackRed      : 14
% 2.14/1.26  
% 2.14/1.26  #Partial instantiations: 0
% 2.14/1.26  #Strategies tried      : 1
% 2.14/1.26  
% 2.14/1.26  Timing (in seconds)
% 2.14/1.26  ----------------------
% 2.14/1.26  Preprocessing        : 0.32
% 2.14/1.26  Parsing              : 0.17
% 2.14/1.26  CNF conversion       : 0.02
% 2.14/1.26  Main loop            : 0.17
% 2.14/1.26  Inferencing          : 0.06
% 2.14/1.26  Reduction            : 0.05
% 2.14/1.26  Demodulation         : 0.04
% 2.14/1.26  BG Simplification    : 0.01
% 2.14/1.26  Subsumption          : 0.03
% 2.14/1.26  Abstraction          : 0.01
% 2.14/1.26  MUC search           : 0.00
% 2.14/1.26  Cooper               : 0.00
% 2.14/1.26  Total                : 0.52
% 2.14/1.26  Index Insertion      : 0.00
% 2.14/1.26  Index Deletion       : 0.00
% 2.14/1.26  Index Matching       : 0.00
% 2.14/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
