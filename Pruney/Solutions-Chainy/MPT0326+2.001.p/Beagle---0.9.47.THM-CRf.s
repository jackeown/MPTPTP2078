%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 140 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 278 expanded)
%              Number of equality atoms :   28 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_271,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_292,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_271,c_2])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_303,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_292,c_34])).

tff(c_105,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_2'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [A_41,B_42] :
      ( ~ v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_123,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_34])).

tff(c_36,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_75,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_194,plain,(
    ! [B_58,D_59,A_60,C_61] :
      ( r1_tarski(B_58,D_59)
      | k2_zfmisc_1(A_60,B_58) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_60,B_58),k2_zfmisc_1(C_61,D_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_200,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_194])).

tff(c_220,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_200])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | k2_zfmisc_1(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_24])).

tff(c_242,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [B_31,A_32] :
      ( ~ r1_xboole_0(B_31,A_32)
      | ~ r1_tarski(B_31,A_32)
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_247,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_82])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_247])).

tff(c_254,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_261,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_82])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_261])).

tff(c_268,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_388,plain,(
    ! [B_89,D_90,A_91,C_92] :
      ( r1_tarski(B_89,D_90)
      | k2_zfmisc_1(A_91,B_89) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_91,B_89),k2_zfmisc_1(C_92,D_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_412,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_388])).

tff(c_417,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_432,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_24])).

tff(c_434,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_319,plain,(
    ! [B_74,A_75] :
      ( ~ r1_xboole_0(B_74,A_75)
      | ~ r1_tarski(B_74,A_75)
      | v1_xboole_0(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_322,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_319])).

tff(c_325,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_322])).

tff(c_452,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_325])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_452])).

tff(c_459,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_466,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_325])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_466])).

tff(c_474,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_488,plain,(
    ! [A_93,C_94,B_95,D_96] :
      ( r1_tarski(A_93,C_94)
      | k2_zfmisc_1(A_93,B_95) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_93,B_95),k2_zfmisc_1(C_94,D_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_494,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_488])).

tff(c_514,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_494])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.29  
% 2.40/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.40/1.29  
% 2.40/1.29  %Foreground sorts:
% 2.40/1.29  
% 2.40/1.29  
% 2.40/1.29  %Background operators:
% 2.40/1.29  
% 2.40/1.29  
% 2.40/1.29  %Foreground operators:
% 2.40/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.40/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.40/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.40/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.29  
% 2.40/1.31  tff(f_89, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.40/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.40/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.40/1.31  tff(f_78, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.40/1.31  tff(f_70, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.40/1.31  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.31  tff(f_56, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.40/1.31  tff(f_64, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.40/1.31  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.31  tff(c_271, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.31  tff(c_292, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_271, c_2])).
% 2.40/1.31  tff(c_34, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.31  tff(c_303, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_292, c_34])).
% 2.40/1.31  tff(c_105, plain, (![A_39, B_40]: (r2_hidden('#skF_2'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.31  tff(c_116, plain, (![A_41, B_42]: (~v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_105, c_2])).
% 2.40/1.31  tff(c_123, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_116, c_34])).
% 2.40/1.31  tff(c_36, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.31  tff(c_75, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.40/1.31  tff(c_194, plain, (![B_58, D_59, A_60, C_61]: (r1_tarski(B_58, D_59) | k2_zfmisc_1(A_60, B_58)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_60, B_58), k2_zfmisc_1(C_61, D_59)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.31  tff(c_200, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_194])).
% 2.40/1.31  tff(c_220, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_200])).
% 2.40/1.31  tff(c_24, plain, (![B_16, A_15]: (k1_xboole_0=B_16 | k1_xboole_0=A_15 | k2_zfmisc_1(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.40/1.31  tff(c_240, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_220, c_24])).
% 2.40/1.31  tff(c_242, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_240])).
% 2.40/1.31  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.31  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.31  tff(c_76, plain, (![B_31, A_32]: (~r1_xboole_0(B_31, A_32) | ~r1_tarski(B_31, A_32) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.31  tff(c_79, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_76])).
% 2.40/1.31  tff(c_82, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 2.40/1.31  tff(c_247, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_82])).
% 2.40/1.31  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_247])).
% 2.40/1.31  tff(c_254, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_240])).
% 2.40/1.31  tff(c_261, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_82])).
% 2.40/1.31  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_261])).
% 2.40/1.31  tff(c_268, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_36])).
% 2.40/1.31  tff(c_388, plain, (![B_89, D_90, A_91, C_92]: (r1_tarski(B_89, D_90) | k2_zfmisc_1(A_91, B_89)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_91, B_89), k2_zfmisc_1(C_92, D_90)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.31  tff(c_412, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_388])).
% 2.40/1.31  tff(c_417, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_412])).
% 2.40/1.31  tff(c_432, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_417, c_24])).
% 2.40/1.31  tff(c_434, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_432])).
% 2.40/1.31  tff(c_319, plain, (![B_74, A_75]: (~r1_xboole_0(B_74, A_75) | ~r1_tarski(B_74, A_75) | v1_xboole_0(B_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.31  tff(c_322, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_319])).
% 2.40/1.31  tff(c_325, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_322])).
% 2.40/1.31  tff(c_452, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_325])).
% 2.40/1.31  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_452])).
% 2.40/1.31  tff(c_459, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_432])).
% 2.40/1.31  tff(c_466, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_325])).
% 2.40/1.31  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_466])).
% 2.40/1.31  tff(c_474, plain, (k2_zfmisc_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_412])).
% 2.40/1.31  tff(c_488, plain, (![A_93, C_94, B_95, D_96]: (r1_tarski(A_93, C_94) | k2_zfmisc_1(A_93, B_95)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_93, B_95), k2_zfmisc_1(C_94, D_96)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.31  tff(c_494, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_488])).
% 2.40/1.31  tff(c_514, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_494])).
% 2.40/1.31  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_514])).
% 2.40/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  Inference rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Ref     : 0
% 2.40/1.31  #Sup     : 95
% 2.40/1.31  #Fact    : 0
% 2.40/1.31  #Define  : 0
% 2.40/1.31  #Split   : 6
% 2.40/1.31  #Chain   : 0
% 2.40/1.31  #Close   : 0
% 2.40/1.31  
% 2.40/1.31  Ordering : KBO
% 2.40/1.31  
% 2.40/1.31  Simplification rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Subsume      : 8
% 2.40/1.31  #Demod        : 81
% 2.40/1.31  #Tautology    : 42
% 2.40/1.31  #SimpNegUnit  : 8
% 2.40/1.31  #BackRed      : 42
% 2.40/1.31  
% 2.40/1.31  #Partial instantiations: 0
% 2.40/1.31  #Strategies tried      : 1
% 2.40/1.31  
% 2.40/1.31  Timing (in seconds)
% 2.40/1.31  ----------------------
% 2.40/1.31  Preprocessing        : 0.28
% 2.40/1.31  Parsing              : 0.15
% 2.40/1.31  CNF conversion       : 0.02
% 2.40/1.31  Main loop            : 0.27
% 2.40/1.31  Inferencing          : 0.09
% 2.40/1.31  Reduction            : 0.08
% 2.40/1.31  Demodulation         : 0.05
% 2.40/1.31  BG Simplification    : 0.02
% 2.40/1.31  Subsumption          : 0.06
% 2.40/1.31  Abstraction          : 0.01
% 2.40/1.31  MUC search           : 0.00
% 2.40/1.31  Cooper               : 0.00
% 2.40/1.31  Total                : 0.58
% 2.40/1.31  Index Insertion      : 0.00
% 2.40/1.31  Index Deletion       : 0.00
% 2.40/1.31  Index Matching       : 0.00
% 2.40/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
