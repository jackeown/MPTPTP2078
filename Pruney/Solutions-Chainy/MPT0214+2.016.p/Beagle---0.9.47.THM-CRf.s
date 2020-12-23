%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:32 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 132 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 188 expanded)
%              Number of equality atoms :   32 (  82 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_62,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,(
    ! [B_49,A_50] :
      ( ~ r2_hidden(B_49,A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [C_20] : ~ v1_xboole_0(k1_tarski(C_20)) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_102,plain,(
    ! [A_56] :
      ( v1_xboole_0(A_56)
      | r2_hidden('#skF_1'(A_56),A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [A_16] :
      ( '#skF_1'(k1_tarski(A_16)) = A_16
      | v1_xboole_0(k1_tarski(A_16)) ) ),
    inference(resolution,[status(thm)],[c_102,c_32])).

tff(c_112,plain,(
    ! [A_16] : '#skF_1'(k1_tarski(A_16)) = A_16 ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_106])).

tff(c_22,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_281,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_298,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_281])).

tff(c_303,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_321,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_34])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_180,plain,(
    ! [B_65] : k3_xboole_0(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_24,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_194,plain,(
    ! [B_66] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_24])).

tff(c_185,plain,(
    ! [B_65] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_24])).

tff(c_204,plain,(
    ! [B_68,B_67] : k4_xboole_0(k1_xboole_0,B_68) = k4_xboole_0(k1_xboole_0,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_185])).

tff(c_30,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_220,plain,(
    ! [B_68] : k4_xboole_0(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_30])).

tff(c_246,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_185])).

tff(c_425,plain,(
    ! [A_97,C_98,B_99] :
      ( ~ r2_hidden(A_97,C_98)
      | ~ r2_hidden(A_97,B_99)
      | ~ r2_hidden(A_97,k5_xboole_0(B_99,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_445,plain,(
    ! [A_100] :
      ( ~ r2_hidden(A_100,k1_xboole_0)
      | ~ r2_hidden(A_100,k1_xboole_0)
      | ~ r2_hidden(A_100,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_425])).

tff(c_447,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_321,c_445])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_447])).

tff(c_455,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_156,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_146])).

tff(c_203,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_457,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_203])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_457])).

tff(c_462,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_469,plain,(
    '#skF_1'(k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_112])).

tff(c_480,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_469])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  %$ r2_hidden > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.29  
% 2.16/1.30  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.16/1.30  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.16/1.30  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.30  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.16/1.30  tff(f_48, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.16/1.30  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.16/1.30  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.30  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.16/1.30  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.16/1.30  tff(c_62, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.30  tff(c_34, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.30  tff(c_89, plain, (![B_49, A_50]: (~r2_hidden(B_49, A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.30  tff(c_93, plain, (![C_20]: (~v1_xboole_0(k1_tarski(C_20)))), inference(resolution, [status(thm)], [c_34, c_89])).
% 2.16/1.30  tff(c_102, plain, (![A_56]: (v1_xboole_0(A_56) | r2_hidden('#skF_1'(A_56), A_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.30  tff(c_32, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.30  tff(c_106, plain, (![A_16]: ('#skF_1'(k1_tarski(A_16))=A_16 | v1_xboole_0(k1_tarski(A_16)))), inference(resolution, [status(thm)], [c_102, c_32])).
% 2.16/1.30  tff(c_112, plain, (![A_16]: ('#skF_1'(k1_tarski(A_16))=A_16)), inference(negUnitSimplification, [status(thm)], [c_93, c_106])).
% 2.16/1.30  tff(c_22, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.30  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.30  tff(c_281, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.30  tff(c_298, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_281])).
% 2.16/1.30  tff(c_303, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_298])).
% 2.16/1.30  tff(c_321, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_303, c_34])).
% 2.16/1.30  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.30  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.16/1.30  tff(c_146, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.30  tff(c_162, plain, (![A_64]: (k1_xboole_0=A_64 | ~r1_tarski(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_146])).
% 2.16/1.30  tff(c_180, plain, (![B_65]: (k3_xboole_0(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_162])).
% 2.16/1.30  tff(c_24, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.30  tff(c_194, plain, (![B_66]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_180, c_24])).
% 2.16/1.30  tff(c_185, plain, (![B_65]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_65))), inference(superposition, [status(thm), theory('equality')], [c_180, c_24])).
% 2.16/1.30  tff(c_204, plain, (![B_68, B_67]: (k4_xboole_0(k1_xboole_0, B_68)=k4_xboole_0(k1_xboole_0, B_67))), inference(superposition, [status(thm), theory('equality')], [c_194, c_185])).
% 2.16/1.30  tff(c_30, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.30  tff(c_220, plain, (![B_68]: (k4_xboole_0(k1_xboole_0, B_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_30])).
% 2.16/1.30  tff(c_246, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_220, c_185])).
% 2.16/1.30  tff(c_425, plain, (![A_97, C_98, B_99]: (~r2_hidden(A_97, C_98) | ~r2_hidden(A_97, B_99) | ~r2_hidden(A_97, k5_xboole_0(B_99, C_98)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.30  tff(c_445, plain, (![A_100]: (~r2_hidden(A_100, k1_xboole_0) | ~r2_hidden(A_100, k1_xboole_0) | ~r2_hidden(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_246, c_425])).
% 2.16/1.30  tff(c_447, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_321, c_445])).
% 2.16/1.30  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_321, c_447])).
% 2.16/1.30  tff(c_455, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_298])).
% 2.16/1.30  tff(c_156, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_146])).
% 2.16/1.30  tff(c_203, plain, (~r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.16/1.30  tff(c_457, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_203])).
% 2.16/1.30  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_457])).
% 2.16/1.30  tff(c_462, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_156])).
% 2.16/1.30  tff(c_469, plain, ('#skF_1'(k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_462, c_112])).
% 2.16/1.30  tff(c_480, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_469])).
% 2.16/1.30  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_480])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 103
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 2
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 16
% 2.16/1.30  #Demod        : 30
% 2.16/1.30  #Tautology    : 62
% 2.16/1.30  #SimpNegUnit  : 5
% 2.16/1.30  #BackRed      : 6
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.49/1.31  Preprocessing        : 0.32
% 2.49/1.31  Parsing              : 0.17
% 2.49/1.31  CNF conversion       : 0.02
% 2.49/1.31  Main loop            : 0.23
% 2.49/1.31  Inferencing          : 0.08
% 2.49/1.31  Reduction            : 0.07
% 2.49/1.31  Demodulation         : 0.05
% 2.49/1.31  BG Simplification    : 0.02
% 2.49/1.31  Subsumption          : 0.04
% 2.49/1.31  Abstraction          : 0.01
% 2.49/1.31  MUC search           : 0.00
% 2.49/1.31  Cooper               : 0.00
% 2.49/1.31  Total                : 0.58
% 2.49/1.31  Index Insertion      : 0.00
% 2.49/1.31  Index Deletion       : 0.00
% 2.49/1.31  Index Matching       : 0.00
% 2.49/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
