%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:54 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   59 (  63 expanded)
%              Number of leaves         :   32 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  54 expanded)
%              Number of equality atoms :   38 (  42 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_70,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_220,plain,(
    ! [B_77,C_78,A_79] : k1_enumset1(B_77,C_78,A_79) = k1_enumset1(A_79,B_77,C_78) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_273,plain,(
    ! [B_38,A_37] : k1_enumset1(B_38,A_37,A_37) = k2_tarski(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_220])).

tff(c_66,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_835,plain,(
    ! [A_105,B_106,C_107] : k2_xboole_0(k1_tarski(A_105),k2_tarski(B_106,C_107)) = k1_enumset1(A_105,B_106,C_107) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_844,plain,(
    ! [A_105,A_36] : k2_xboole_0(k1_tarski(A_105),k1_tarski(A_36)) = k1_enumset1(A_105,A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_835])).

tff(c_1123,plain,(
    ! [A_118,A_119] : k2_xboole_0(k1_tarski(A_118),k1_tarski(A_119)) = k2_tarski(A_119,A_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_844])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_669,plain,(
    ! [A_97,B_98] : k5_xboole_0(k5_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = k2_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_690,plain,(
    ! [A_11] : k5_xboole_0(A_11,k3_xboole_0(A_11,k1_xboole_0)) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_669])).

tff(c_696,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8,c_690])).

tff(c_72,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_147,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_151,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_147])).

tff(c_365,plain,(
    ! [A_85,B_86] : k2_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_380,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k2_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_365])).

tff(c_699,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_380])).

tff(c_1129,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_699])).

tff(c_164,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [E_24,B_19,C_20] : r2_hidden(E_24,k1_enumset1(E_24,B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_170,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_32])).

tff(c_1157,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_170])).

tff(c_50,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1776,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1157,c_50])).

tff(c_1812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.52  
% 2.97/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.97/1.52  
% 2.97/1.52  %Foreground sorts:
% 2.97/1.52  
% 2.97/1.52  
% 2.97/1.52  %Background operators:
% 2.97/1.52  
% 2.97/1.52  
% 2.97/1.52  %Foreground operators:
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.97/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.97/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.97/1.52  
% 2.97/1.53  tff(f_86, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.97/1.53  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.97/1.53  tff(f_75, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 2.97/1.53  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.97/1.53  tff(f_77, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.97/1.53  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.97/1.53  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.97/1.53  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.97/1.53  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.97/1.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.97/1.53  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.97/1.53  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.97/1.53  tff(c_70, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.97/1.53  tff(c_68, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.53  tff(c_220, plain, (![B_77, C_78, A_79]: (k1_enumset1(B_77, C_78, A_79)=k1_enumset1(A_79, B_77, C_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.53  tff(c_273, plain, (![B_38, A_37]: (k1_enumset1(B_38, A_37, A_37)=k2_tarski(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_68, c_220])).
% 2.97/1.53  tff(c_66, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.97/1.53  tff(c_835, plain, (![A_105, B_106, C_107]: (k2_xboole_0(k1_tarski(A_105), k2_tarski(B_106, C_107))=k1_enumset1(A_105, B_106, C_107))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.53  tff(c_844, plain, (![A_105, A_36]: (k2_xboole_0(k1_tarski(A_105), k1_tarski(A_36))=k1_enumset1(A_105, A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_66, c_835])).
% 2.97/1.53  tff(c_1123, plain, (![A_118, A_119]: (k2_xboole_0(k1_tarski(A_118), k1_tarski(A_119))=k2_tarski(A_119, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_844])).
% 2.97/1.53  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.97/1.53  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.53  tff(c_669, plain, (![A_97, B_98]: (k5_xboole_0(k5_xboole_0(A_97, B_98), k3_xboole_0(A_97, B_98))=k2_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.97/1.53  tff(c_690, plain, (![A_11]: (k5_xboole_0(A_11, k3_xboole_0(A_11, k1_xboole_0))=k2_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_669])).
% 2.97/1.53  tff(c_696, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8, c_690])).
% 2.97/1.53  tff(c_72, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.97/1.53  tff(c_147, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.53  tff(c_151, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_147])).
% 2.97/1.53  tff(c_365, plain, (![A_85, B_86]: (k2_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.53  tff(c_380, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k2_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_151, c_365])).
% 2.97/1.53  tff(c_699, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_380])).
% 2.97/1.53  tff(c_1129, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1123, c_699])).
% 2.97/1.53  tff(c_164, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.53  tff(c_32, plain, (![E_24, B_19, C_20]: (r2_hidden(E_24, k1_enumset1(E_24, B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.97/1.53  tff(c_170, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_32])).
% 2.97/1.53  tff(c_1157, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1129, c_170])).
% 2.97/1.53  tff(c_50, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.97/1.53  tff(c_1776, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1157, c_50])).
% 2.97/1.53  tff(c_1812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1776])).
% 2.97/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.53  
% 2.97/1.53  Inference rules
% 2.97/1.53  ----------------------
% 2.97/1.53  #Ref     : 0
% 2.97/1.53  #Sup     : 320
% 2.97/1.53  #Fact    : 0
% 2.97/1.53  #Define  : 0
% 2.97/1.53  #Split   : 0
% 2.97/1.53  #Chain   : 0
% 2.97/1.53  #Close   : 0
% 2.97/1.53  
% 2.97/1.53  Ordering : KBO
% 2.97/1.53  
% 2.97/1.53  Simplification rules
% 2.97/1.53  ----------------------
% 2.97/1.53  #Subsume      : 6
% 2.97/1.53  #Demod        : 169
% 2.97/1.53  #Tautology    : 211
% 2.97/1.53  #SimpNegUnit  : 1
% 2.97/1.53  #BackRed      : 5
% 2.97/1.53  
% 2.97/1.53  #Partial instantiations: 714
% 2.97/1.53  #Strategies tried      : 1
% 2.97/1.53  
% 2.97/1.53  Timing (in seconds)
% 2.97/1.53  ----------------------
% 2.97/1.53  Preprocessing        : 0.33
% 2.97/1.53  Parsing              : 0.17
% 2.97/1.53  CNF conversion       : 0.03
% 2.97/1.53  Main loop            : 0.44
% 2.97/1.53  Inferencing          : 0.19
% 2.97/1.53  Reduction            : 0.14
% 2.97/1.53  Demodulation         : 0.11
% 2.97/1.53  BG Simplification    : 0.02
% 2.97/1.53  Subsumption          : 0.06
% 2.97/1.53  Abstraction          : 0.02
% 2.97/1.53  MUC search           : 0.00
% 2.97/1.53  Cooper               : 0.00
% 2.97/1.53  Total                : 0.80
% 2.97/1.53  Index Insertion      : 0.00
% 2.97/1.53  Index Deletion       : 0.00
% 2.97/1.53  Index Matching       : 0.00
% 2.97/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
