%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:37 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   58 (  81 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  94 expanded)
%              Number of equality atoms :   39 (  74 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_26,plain,(
    ! [B_37] : ~ r1_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,B_48)
      | k3_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [B_37] : k3_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_26])).

tff(c_32,plain,
    ( '#skF_2' != '#skF_1'
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),k1_tarski(B_39))
      | B_39 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k1_xboole_0
      | B_59 = A_58 ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k5_xboole_0(k1_tarski(A_58),k1_xboole_0)
      | B_59 = A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_170,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(k1_tarski(A_65),k1_tarski(B_66)) = k1_tarski(A_65)
      | B_66 = A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_30,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1')
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_73,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_179,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_73])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_179])).

tff(c_195,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_196,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_383,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_195,c_196,c_34])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_220,plain,(
    ! [A_6,B_7] : k3_xboole_0(k4_xboole_0(A_6,B_7),B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_208])).

tff(c_393,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_220])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_393])).

tff(c_406,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_407,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( '#skF_2' != '#skF_1'
    | k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_462,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_406,c_407,c_36])).

tff(c_466,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_10])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:19:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.27  %$ r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.04/1.27  
% 2.04/1.27  %Foreground sorts:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Background operators:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Foreground operators:
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.04/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.27  
% 2.04/1.28  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.04/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.04/1.28  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.04/1.28  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.04/1.28  tff(f_59, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.04/1.28  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.04/1.28  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.04/1.28  tff(c_26, plain, (![B_37]: (~r1_xboole_0(k1_tarski(B_37), k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_67, plain, (![A_47, B_48]: (r1_xboole_0(A_47, B_48) | k3_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_71, plain, (![B_37]: (k3_xboole_0(k1_tarski(B_37), k1_tarski(B_37))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_26])).
% 2.04/1.28  tff(c_32, plain, ('#skF_2'!='#skF_1' | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.28  tff(c_37, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_32])).
% 2.04/1.28  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.28  tff(c_28, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), k1_tarski(B_39)) | B_39=A_38)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.28  tff(c_81, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_116, plain, (![A_58, B_59]: (k3_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k1_xboole_0 | B_59=A_58)), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.04/1.28  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.28  tff(c_122, plain, (![A_58, B_59]: (k4_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k5_xboole_0(k1_tarski(A_58), k1_xboole_0) | B_59=A_58)), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 2.04/1.28  tff(c_170, plain, (![A_65, B_66]: (k4_xboole_0(k1_tarski(A_65), k1_tarski(B_66))=k1_tarski(A_65) | B_66=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_122])).
% 2.04/1.28  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1') | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.28  tff(c_73, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 2.04/1.28  tff(c_179, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_170, c_73])).
% 2.04/1.28  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_179])).
% 2.04/1.28  tff(c_195, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.04/1.28  tff(c_196, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.04/1.28  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.28  tff(c_383, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_195, c_196, c_34])).
% 2.04/1.28  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.28  tff(c_208, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_220, plain, (![A_6, B_7]: (k3_xboole_0(k4_xboole_0(A_6, B_7), B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_208])).
% 2.04/1.28  tff(c_393, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_383, c_220])).
% 2.04/1.28  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_393])).
% 2.04/1.28  tff(c_406, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 2.04/1.28  tff(c_407, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.04/1.28  tff(c_36, plain, ('#skF_2'!='#skF_1' | k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.28  tff(c_462, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_406, c_407, c_36])).
% 2.04/1.28  tff(c_466, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_462, c_10])).
% 2.04/1.28  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_466])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 102
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 2
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 5
% 2.04/1.28  #Demod        : 32
% 2.04/1.28  #Tautology    : 78
% 2.04/1.28  #SimpNegUnit  : 7
% 2.04/1.28  #BackRed      : 0
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.30
% 2.04/1.28  Parsing              : 0.16
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.20
% 2.04/1.28  Inferencing          : 0.08
% 2.04/1.28  Reduction            : 0.06
% 2.04/1.28  Demodulation         : 0.04
% 2.04/1.28  BG Simplification    : 0.01
% 2.04/1.28  Subsumption          : 0.02
% 2.04/1.28  Abstraction          : 0.01
% 2.04/1.28  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.52
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
