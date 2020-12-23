%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   34 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  65 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_46,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [A_66,B_67] : k4_xboole_0(k1_tarski(A_66),k2_tarski(A_66,B_67)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,(
    ! [A_13] : k4_xboole_0(k1_tarski(A_13),k1_tarski(A_13)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_38,plain,(
    ! [B_48] : k4_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) != k1_tarski(B_48) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_102,plain,(
    ! [B_48] : k1_tarski(B_48) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_38])).

tff(c_12,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [A_82,B_83] :
      ( ~ r1_xboole_0(A_82,B_83)
      | k3_xboole_0(A_82,B_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_192,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_48,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_246,plain,(
    ! [B_89,A_90] :
      ( k1_tarski(B_89) = A_90
      | k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k1_tarski(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_256,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_246])).

tff(c_286,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_36,plain,(
    ! [A_45,B_46] : k3_xboole_0(k1_tarski(A_45),k2_tarski(A_45,B_46)) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_292,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_36])).

tff(c_301,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_292])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_301])).

tff(c_304,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_34,plain,(
    ! [A_43,B_44] : r1_tarski(k1_tarski(A_43),k2_tarski(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_318,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_34])).

tff(c_44,plain,(
    ! [B_52,A_51] :
      ( B_52 = A_51
      | ~ r1_tarski(k1_tarski(A_51),k1_tarski(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_327,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_318,c_44])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:07:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.08/1.32  
% 2.08/1.32  %Foreground sorts:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Background operators:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Foreground operators:
% 2.08/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.32  
% 2.08/1.33  tff(f_93, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.08/1.33  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.33  tff(f_84, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.08/1.33  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.08/1.33  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.08/1.33  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.08/1.33  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.33  tff(f_73, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.08/1.33  tff(f_77, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.08/1.33  tff(f_75, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.08/1.33  tff(f_88, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.08/1.33  tff(c_46, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.33  tff(c_14, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.33  tff(c_92, plain, (![A_66, B_67]: (k4_xboole_0(k1_tarski(A_66), k2_tarski(A_66, B_67))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.08/1.33  tff(c_99, plain, (![A_13]: (k4_xboole_0(k1_tarski(A_13), k1_tarski(A_13))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_92])).
% 2.08/1.33  tff(c_38, plain, (![B_48]: (k4_xboole_0(k1_tarski(B_48), k1_tarski(B_48))!=k1_tarski(B_48))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.08/1.33  tff(c_102, plain, (![B_48]: (k1_tarski(B_48)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_38])).
% 2.08/1.33  tff(c_12, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.33  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.33  tff(c_164, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.33  tff(c_188, plain, (![A_82, B_83]: (~r1_xboole_0(A_82, B_83) | k3_xboole_0(A_82, B_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_164])).
% 2.08/1.33  tff(c_192, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_188])).
% 2.08/1.33  tff(c_48, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.33  tff(c_246, plain, (![B_89, A_90]: (k1_tarski(B_89)=A_90 | k1_xboole_0=A_90 | ~r1_tarski(A_90, k1_tarski(B_89)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.33  tff(c_256, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_246])).
% 2.08/1.33  tff(c_286, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_256])).
% 2.08/1.33  tff(c_36, plain, (![A_45, B_46]: (k3_xboole_0(k1_tarski(A_45), k2_tarski(A_45, B_46))=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.33  tff(c_292, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_286, c_36])).
% 2.08/1.33  tff(c_301, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_192, c_292])).
% 2.08/1.33  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_301])).
% 2.08/1.33  tff(c_304, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_256])).
% 2.08/1.33  tff(c_34, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), k2_tarski(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.08/1.33  tff(c_318, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_304, c_34])).
% 2.08/1.33  tff(c_44, plain, (![B_52, A_51]: (B_52=A_51 | ~r1_tarski(k1_tarski(A_51), k1_tarski(B_52)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.33  tff(c_327, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_318, c_44])).
% 2.08/1.33  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_327])).
% 2.08/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  Inference rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Ref     : 0
% 2.08/1.33  #Sup     : 63
% 2.08/1.33  #Fact    : 0
% 2.08/1.33  #Define  : 0
% 2.08/1.33  #Split   : 1
% 2.08/1.33  #Chain   : 0
% 2.08/1.33  #Close   : 0
% 2.08/1.33  
% 2.08/1.33  Ordering : KBO
% 2.08/1.33  
% 2.08/1.33  Simplification rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Subsume      : 2
% 2.08/1.33  #Demod        : 13
% 2.08/1.33  #Tautology    : 45
% 2.08/1.33  #SimpNegUnit  : 7
% 2.08/1.33  #BackRed      : 4
% 2.08/1.33  
% 2.08/1.33  #Partial instantiations: 0
% 2.08/1.33  #Strategies tried      : 1
% 2.08/1.33  
% 2.08/1.33  Timing (in seconds)
% 2.08/1.33  ----------------------
% 2.08/1.33  Preprocessing        : 0.34
% 2.08/1.33  Parsing              : 0.19
% 2.08/1.33  CNF conversion       : 0.02
% 2.08/1.33  Main loop            : 0.17
% 2.08/1.33  Inferencing          : 0.06
% 2.08/1.33  Reduction            : 0.06
% 2.08/1.33  Demodulation         : 0.04
% 2.08/1.33  BG Simplification    : 0.01
% 2.08/1.33  Subsumption          : 0.03
% 2.08/1.33  Abstraction          : 0.01
% 2.08/1.33  MUC search           : 0.00
% 2.08/1.33  Cooper               : 0.00
% 2.08/1.33  Total                : 0.54
% 2.08/1.33  Index Insertion      : 0.00
% 2.08/1.33  Index Deletion       : 0.00
% 2.08/1.33  Index Matching       : 0.00
% 2.08/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
