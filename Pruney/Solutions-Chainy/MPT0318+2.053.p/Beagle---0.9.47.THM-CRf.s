%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:08 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  84 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_7] : k3_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_253,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_253])).

tff(c_266,plain,(
    ! [A_98] : k4_xboole_0(k1_xboole_0,A_98) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_38,plain,(
    ! [B_46,A_45] :
      ( ~ r2_hidden(B_46,A_45)
      | k4_xboole_0(A_45,k1_tarski(B_46)) != A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_284,plain,(
    ! [B_46] : ~ r2_hidden(B_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_38])).

tff(c_98,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_98])).

tff(c_110,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_128,plain,(
    ! [B_61,A_62] :
      ( ~ r2_hidden(B_61,A_62)
      | k4_xboole_0(A_62,k1_tarski(B_61)) != A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_136,plain,(
    ! [B_61] : ~ r2_hidden(B_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_128])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_214,plain,(
    ! [C_90,B_91,D_92] :
      ( r2_hidden(k4_tarski(C_90,B_91),k2_zfmisc_1(k1_tarski(C_90),D_92))
      | ~ r2_hidden(B_91,D_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_227,plain,(
    ! [B_91] :
      ( r2_hidden(k4_tarski('#skF_3',B_91),k1_xboole_0)
      | ~ r2_hidden(B_91,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_214])).

tff(c_233,plain,(
    ! [B_93] : ~ r2_hidden(B_93,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_227])).

tff(c_237,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2,c_233])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_237])).

tff(c_242,plain,(
    k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_406,plain,(
    ! [A_133,D_134,C_135] :
      ( r2_hidden(k4_tarski(A_133,D_134),k2_zfmisc_1(C_135,k1_tarski(D_134)))
      | ~ r2_hidden(A_133,C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_423,plain,(
    ! [A_133] :
      ( r2_hidden(k4_tarski(A_133,'#skF_3'),k1_xboole_0)
      | ~ r2_hidden(A_133,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_406])).

tff(c_430,plain,(
    ! [A_136] : ~ r2_hidden(A_136,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_423])).

tff(c_434,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2,c_430])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:30 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  
% 2.13/1.30  tff(f_84, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.13/1.30  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.13/1.30  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.13/1.30  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.13/1.30  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.30  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.13/1.30  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.13/1.30  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.13/1.30  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.13/1.30  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.30  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.30  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.30  tff(c_72, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.30  tff(c_76, plain, (![A_7]: (k3_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 2.13/1.30  tff(c_253, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.30  tff(c_262, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_76, c_253])).
% 2.13/1.30  tff(c_266, plain, (![A_98]: (k4_xboole_0(k1_xboole_0, A_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 2.13/1.30  tff(c_38, plain, (![B_46, A_45]: (~r2_hidden(B_46, A_45) | k4_xboole_0(A_45, k1_tarski(B_46))!=A_45)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_284, plain, (![B_46]: (~r2_hidden(B_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_266, c_38])).
% 2.13/1.30  tff(c_98, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.30  tff(c_107, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_76, c_98])).
% 2.13/1.30  tff(c_110, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_107])).
% 2.13/1.30  tff(c_128, plain, (![B_61, A_62]: (~r2_hidden(B_61, A_62) | k4_xboole_0(A_62, k1_tarski(B_61))!=A_62)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_136, plain, (![B_61]: (~r2_hidden(B_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_128])).
% 2.13/1.30  tff(c_42, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.30  tff(c_93, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.13/1.30  tff(c_214, plain, (![C_90, B_91, D_92]: (r2_hidden(k4_tarski(C_90, B_91), k2_zfmisc_1(k1_tarski(C_90), D_92)) | ~r2_hidden(B_91, D_92))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.30  tff(c_227, plain, (![B_91]: (r2_hidden(k4_tarski('#skF_3', B_91), k1_xboole_0) | ~r2_hidden(B_91, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_214])).
% 2.13/1.30  tff(c_233, plain, (![B_93]: (~r2_hidden(B_93, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_136, c_227])).
% 2.13/1.30  tff(c_237, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2, c_233])).
% 2.13/1.30  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_237])).
% 2.13/1.30  tff(c_242, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.13/1.30  tff(c_406, plain, (![A_133, D_134, C_135]: (r2_hidden(k4_tarski(A_133, D_134), k2_zfmisc_1(C_135, k1_tarski(D_134))) | ~r2_hidden(A_133, C_135))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.13/1.30  tff(c_423, plain, (![A_133]: (r2_hidden(k4_tarski(A_133, '#skF_3'), k1_xboole_0) | ~r2_hidden(A_133, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_406])).
% 2.13/1.30  tff(c_430, plain, (![A_136]: (~r2_hidden(A_136, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_284, c_423])).
% 2.13/1.30  tff(c_434, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2, c_430])).
% 2.13/1.30  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_434])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 81
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 3
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 8
% 2.13/1.30  #Demod        : 16
% 2.13/1.30  #Tautology    : 55
% 2.13/1.30  #SimpNegUnit  : 6
% 2.13/1.30  #BackRed      : 11
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.33
% 2.13/1.30  Parsing              : 0.18
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.21
% 2.13/1.30  Inferencing          : 0.08
% 2.13/1.30  Reduction            : 0.06
% 2.13/1.30  Demodulation         : 0.04
% 2.13/1.30  BG Simplification    : 0.02
% 2.13/1.30  Subsumption          : 0.03
% 2.13/1.30  Abstraction          : 0.01
% 2.13/1.30  MUC search           : 0.00
% 2.13/1.30  Cooper               : 0.00
% 2.13/1.30  Total                : 0.56
% 2.13/1.30  Index Insertion      : 0.00
% 2.13/1.30  Index Deletion       : 0.00
% 2.13/1.30  Index Matching       : 0.00
% 2.13/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
