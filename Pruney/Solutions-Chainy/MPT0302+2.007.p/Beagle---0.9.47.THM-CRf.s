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
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 107 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 186 expanded)
%              Number of equality atoms :   30 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_46,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_373,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,A_56)
      | ~ r2_hidden(D_55,k4_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_393,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_56,B_57)),A_56)
      | k4_xboole_0(A_56,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_373])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_743,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( r2_hidden(k4_tarski(A_94,B_95),k2_zfmisc_1(C_96,D_97))
      | ~ r2_hidden(B_95,D_97)
      | ~ r2_hidden(A_94,C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_453,plain,(
    ! [A_68,C_69,B_70,D_71] :
      ( r2_hidden(A_68,C_69)
      | ~ r2_hidden(k4_tarski(A_68,B_70),k2_zfmisc_1(C_69,D_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_456,plain,(
    ! [A_68,B_70] :
      ( r2_hidden(A_68,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_68,B_70),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_453])).

tff(c_762,plain,(
    ! [A_94,B_95] :
      ( r2_hidden(A_94,'#skF_5')
      | ~ r2_hidden(B_95,'#skF_5')
      | ~ r2_hidden(A_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_743,c_456])).

tff(c_803,plain,(
    ! [B_103] : ~ r2_hidden(B_103,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_762])).

tff(c_811,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_803])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_811])).

tff(c_817,plain,(
    ! [A_94] :
      ( r2_hidden(A_94,'#skF_5')
      | ~ r2_hidden(A_94,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_246,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | ~ r2_hidden(D_41,k4_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_823,plain,(
    ! [A_105,B_106] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_105,B_106)),B_106)
      | k4_xboole_0(A_105,B_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_246])).

tff(c_1158,plain,(
    ! [A_122] :
      ( k4_xboole_0(A_122,'#skF_5') = k1_xboole_0
      | ~ r2_hidden('#skF_3'(k4_xboole_0(A_122,'#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_817,c_823])).

tff(c_1171,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_393,c_1158])).

tff(c_26,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1198,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_26])).

tff(c_1205,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1198])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_457,plain,(
    ! [B_72,D_73,A_74,C_75] :
      ( r2_hidden(B_72,D_73)
      | ~ r2_hidden(k4_tarski(A_74,B_72),k2_zfmisc_1(C_75,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_460,plain,(
    ! [B_72,A_74] :
      ( r2_hidden(B_72,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_74,B_72),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_457])).

tff(c_761,plain,(
    ! [B_95,A_94] :
      ( r2_hidden(B_95,'#skF_4')
      | ~ r2_hidden(B_95,'#skF_5')
      | ~ r2_hidden(A_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_743,c_460])).

tff(c_767,plain,(
    ! [A_98] : ~ r2_hidden(A_98,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_761])).

tff(c_775,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_767])).

tff(c_780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_775])).

tff(c_782,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,'#skF_4')
      | ~ r2_hidden(B_99,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_761])).

tff(c_1402,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_3'(k4_xboole_0('#skF_5',B_132)),'#skF_4')
      | k4_xboole_0('#skF_5',B_132) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_393,c_782])).

tff(c_263,plain,(
    ! [A_43,B_42] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_43,B_42)),B_42)
      | k4_xboole_0(A_43,B_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_246])).

tff(c_1437,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1402,c_263])).

tff(c_1471,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1437,c_26])).

tff(c_1479,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_24,c_2,c_1471])).

tff(c_1481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.57  
% 3.15/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.57  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 3.15/1.57  
% 3.15/1.57  %Foreground sorts:
% 3.15/1.57  
% 3.15/1.57  
% 3.15/1.57  %Background operators:
% 3.15/1.57  
% 3.15/1.57  
% 3.15/1.57  %Foreground operators:
% 3.15/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.15/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.15/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.57  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.15/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.57  
% 3.15/1.58  tff(f_77, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.15/1.58  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.58  tff(f_45, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.15/1.58  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.15/1.58  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.15/1.58  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.58  tff(c_46, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.15/1.58  tff(c_24, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.58  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.58  tff(c_373, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, A_56) | ~r2_hidden(D_55, k4_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.58  tff(c_393, plain, (![A_56, B_57]: (r2_hidden('#skF_3'(k4_xboole_0(A_56, B_57)), A_56) | k4_xboole_0(A_56, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_373])).
% 3.15/1.58  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.15/1.58  tff(c_743, plain, (![A_94, B_95, C_96, D_97]: (r2_hidden(k4_tarski(A_94, B_95), k2_zfmisc_1(C_96, D_97)) | ~r2_hidden(B_95, D_97) | ~r2_hidden(A_94, C_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.58  tff(c_52, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.15/1.58  tff(c_453, plain, (![A_68, C_69, B_70, D_71]: (r2_hidden(A_68, C_69) | ~r2_hidden(k4_tarski(A_68, B_70), k2_zfmisc_1(C_69, D_71)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.58  tff(c_456, plain, (![A_68, B_70]: (r2_hidden(A_68, '#skF_5') | ~r2_hidden(k4_tarski(A_68, B_70), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_453])).
% 3.15/1.58  tff(c_762, plain, (![A_94, B_95]: (r2_hidden(A_94, '#skF_5') | ~r2_hidden(B_95, '#skF_5') | ~r2_hidden(A_94, '#skF_4'))), inference(resolution, [status(thm)], [c_743, c_456])).
% 3.15/1.58  tff(c_803, plain, (![B_103]: (~r2_hidden(B_103, '#skF_5'))), inference(splitLeft, [status(thm)], [c_762])).
% 3.15/1.58  tff(c_811, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_803])).
% 3.15/1.58  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_811])).
% 3.15/1.58  tff(c_817, plain, (![A_94]: (r2_hidden(A_94, '#skF_5') | ~r2_hidden(A_94, '#skF_4'))), inference(splitRight, [status(thm)], [c_762])).
% 3.15/1.58  tff(c_246, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | ~r2_hidden(D_41, k4_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.58  tff(c_823, plain, (![A_105, B_106]: (~r2_hidden('#skF_3'(k4_xboole_0(A_105, B_106)), B_106) | k4_xboole_0(A_105, B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_246])).
% 3.15/1.58  tff(c_1158, plain, (![A_122]: (k4_xboole_0(A_122, '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_3'(k4_xboole_0(A_122, '#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_817, c_823])).
% 3.15/1.58  tff(c_1171, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_393, c_1158])).
% 3.15/1.58  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.58  tff(c_1198, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1171, c_26])).
% 3.15/1.58  tff(c_1205, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1198])).
% 3.15/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.58  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.15/1.58  tff(c_457, plain, (![B_72, D_73, A_74, C_75]: (r2_hidden(B_72, D_73) | ~r2_hidden(k4_tarski(A_74, B_72), k2_zfmisc_1(C_75, D_73)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.58  tff(c_460, plain, (![B_72, A_74]: (r2_hidden(B_72, '#skF_4') | ~r2_hidden(k4_tarski(A_74, B_72), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_457])).
% 3.15/1.58  tff(c_761, plain, (![B_95, A_94]: (r2_hidden(B_95, '#skF_4') | ~r2_hidden(B_95, '#skF_5') | ~r2_hidden(A_94, '#skF_4'))), inference(resolution, [status(thm)], [c_743, c_460])).
% 3.15/1.58  tff(c_767, plain, (![A_98]: (~r2_hidden(A_98, '#skF_4'))), inference(splitLeft, [status(thm)], [c_761])).
% 3.15/1.58  tff(c_775, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_767])).
% 3.15/1.58  tff(c_780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_775])).
% 3.15/1.58  tff(c_782, plain, (![B_99]: (r2_hidden(B_99, '#skF_4') | ~r2_hidden(B_99, '#skF_5'))), inference(splitRight, [status(thm)], [c_761])).
% 3.15/1.58  tff(c_1402, plain, (![B_132]: (r2_hidden('#skF_3'(k4_xboole_0('#skF_5', B_132)), '#skF_4') | k4_xboole_0('#skF_5', B_132)=k1_xboole_0)), inference(resolution, [status(thm)], [c_393, c_782])).
% 3.15/1.58  tff(c_263, plain, (![A_43, B_42]: (~r2_hidden('#skF_3'(k4_xboole_0(A_43, B_42)), B_42) | k4_xboole_0(A_43, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_246])).
% 3.15/1.58  tff(c_1437, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1402, c_263])).
% 3.15/1.58  tff(c_1471, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1437, c_26])).
% 3.15/1.58  tff(c_1479, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_24, c_2, c_1471])).
% 3.15/1.58  tff(c_1481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1479])).
% 3.15/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.58  
% 3.15/1.58  Inference rules
% 3.15/1.58  ----------------------
% 3.15/1.58  #Ref     : 0
% 3.15/1.58  #Sup     : 329
% 3.15/1.58  #Fact    : 0
% 3.15/1.58  #Define  : 0
% 3.15/1.58  #Split   : 2
% 3.15/1.58  #Chain   : 0
% 3.15/1.58  #Close   : 0
% 3.15/1.58  
% 3.15/1.58  Ordering : KBO
% 3.15/1.58  
% 3.15/1.58  Simplification rules
% 3.15/1.58  ----------------------
% 3.15/1.58  #Subsume      : 62
% 3.15/1.58  #Demod        : 118
% 3.15/1.58  #Tautology    : 150
% 3.15/1.58  #SimpNegUnit  : 28
% 3.15/1.58  #BackRed      : 3
% 3.15/1.58  
% 3.15/1.58  #Partial instantiations: 0
% 3.15/1.58  #Strategies tried      : 1
% 3.15/1.58  
% 3.15/1.58  Timing (in seconds)
% 3.15/1.58  ----------------------
% 3.15/1.58  Preprocessing        : 0.37
% 3.15/1.58  Parsing              : 0.19
% 3.15/1.58  CNF conversion       : 0.02
% 3.15/1.58  Main loop            : 0.43
% 3.15/1.58  Inferencing          : 0.15
% 3.15/1.58  Reduction            : 0.15
% 3.15/1.58  Demodulation         : 0.11
% 3.15/1.58  BG Simplification    : 0.02
% 3.15/1.58  Subsumption          : 0.08
% 3.15/1.58  Abstraction          : 0.02
% 3.15/1.58  MUC search           : 0.00
% 3.15/1.58  Cooper               : 0.00
% 3.15/1.58  Total                : 0.84
% 3.15/1.58  Index Insertion      : 0.00
% 3.15/1.58  Index Deletion       : 0.00
% 3.15/1.59  Index Matching       : 0.00
% 3.15/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
