%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 214 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(f_64,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_276,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_2'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_294,plain,(
    ! [A_64,B_65] :
      ( ~ v1_xboole_0(A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_276,c_2])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_302,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_294,c_24])).

tff(c_70,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_31,B_32] :
      ( ~ v1_xboole_0(A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_85,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_24])).

tff(c_26,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_156,plain,(
    ! [B_50,D_51,A_52,C_53] :
      ( r1_tarski(B_50,D_51)
      | k2_zfmisc_1(A_52,B_50) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_52,B_50),k2_zfmisc_1(C_53,D_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_166,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_156])).

tff(c_184,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_166])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k1_xboole_0 = B_11
      | k1_xboole_0 = A_10
      | k2_zfmisc_1(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_238,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_14])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_12])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_247])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_271,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_12])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_271])).

tff(c_274,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_338,plain,(
    ! [B_73,D_74,A_75,C_76] :
      ( r1_tarski(B_73,D_74)
      | k2_zfmisc_1(A_75,B_73) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_75,B_73),k2_zfmisc_1(C_76,D_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_364,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_274,c_338])).

tff(c_367,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_382,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_14])).

tff(c_384,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_396,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_12])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_396])).

tff(c_399,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_407,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_12])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_407])).

tff(c_411,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_418,plain,(
    ! [A_77,C_78,B_79,D_80] :
      ( r1_tarski(A_77,C_78)
      | k2_zfmisc_1(A_77,B_79) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_77,B_79),k2_zfmisc_1(C_78,D_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_428,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_274,c_418])).

tff(c_446,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_428])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.09/1.31  
% 2.09/1.31  %Foreground sorts:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Background operators:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Foreground operators:
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.31  
% 2.39/1.32  tff(f_64, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.39/1.32  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.39/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.39/1.32  tff(f_53, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.39/1.32  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.39/1.32  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.39/1.32  tff(c_28, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.32  tff(c_276, plain, (![A_58, B_59]: (r2_hidden('#skF_2'(A_58, B_59), A_58) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.32  tff(c_294, plain, (![A_64, B_65]: (~v1_xboole_0(A_64) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_276, c_2])).
% 2.39/1.32  tff(c_24, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.32  tff(c_302, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_294, c_24])).
% 2.39/1.32  tff(c_70, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.32  tff(c_81, plain, (![A_31, B_32]: (~v1_xboole_0(A_31) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_70, c_2])).
% 2.39/1.32  tff(c_85, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_81, c_24])).
% 2.39/1.32  tff(c_26, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.32  tff(c_69, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.39/1.32  tff(c_156, plain, (![B_50, D_51, A_52, C_53]: (r1_tarski(B_50, D_51) | k2_zfmisc_1(A_52, B_50)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_52, B_50), k2_zfmisc_1(C_53, D_51)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.32  tff(c_166, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_156])).
% 2.39/1.32  tff(c_184, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_24, c_166])).
% 2.39/1.32  tff(c_14, plain, (![B_11, A_10]: (k1_xboole_0=B_11 | k1_xboole_0=A_10 | k2_zfmisc_1(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.32  tff(c_238, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_184, c_14])).
% 2.39/1.32  tff(c_240, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_238])).
% 2.39/1.32  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.39/1.32  tff(c_247, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_12])).
% 2.39/1.32  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_247])).
% 2.39/1.32  tff(c_250, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_238])).
% 2.39/1.32  tff(c_271, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_12])).
% 2.39/1.32  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_271])).
% 2.39/1.32  tff(c_274, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_26])).
% 2.39/1.32  tff(c_338, plain, (![B_73, D_74, A_75, C_76]: (r1_tarski(B_73, D_74) | k2_zfmisc_1(A_75, B_73)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_75, B_73), k2_zfmisc_1(C_76, D_74)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.32  tff(c_364, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_274, c_338])).
% 2.39/1.32  tff(c_367, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_364])).
% 2.39/1.32  tff(c_382, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_367, c_14])).
% 2.39/1.32  tff(c_384, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_382])).
% 2.39/1.32  tff(c_396, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_12])).
% 2.39/1.32  tff(c_398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_302, c_396])).
% 2.39/1.32  tff(c_399, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_382])).
% 2.39/1.32  tff(c_407, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_12])).
% 2.39/1.32  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_407])).
% 2.39/1.32  tff(c_411, plain, (k2_zfmisc_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_364])).
% 2.39/1.32  tff(c_418, plain, (![A_77, C_78, B_79, D_80]: (r1_tarski(A_77, C_78) | k2_zfmisc_1(A_77, B_79)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_77, B_79), k2_zfmisc_1(C_78, D_80)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.32  tff(c_428, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_274, c_418])).
% 2.39/1.32  tff(c_446, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_24, c_428])).
% 2.39/1.32  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_446])).
% 2.39/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  Inference rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Ref     : 0
% 2.39/1.32  #Sup     : 89
% 2.39/1.32  #Fact    : 0
% 2.39/1.32  #Define  : 0
% 2.39/1.32  #Split   : 6
% 2.39/1.32  #Chain   : 0
% 2.39/1.33  #Close   : 0
% 2.39/1.33  
% 2.39/1.33  Ordering : KBO
% 2.39/1.33  
% 2.39/1.33  Simplification rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Subsume      : 9
% 2.39/1.33  #Demod        : 66
% 2.39/1.33  #Tautology    : 34
% 2.39/1.33  #SimpNegUnit  : 8
% 2.39/1.33  #BackRed      : 33
% 2.39/1.33  
% 2.39/1.33  #Partial instantiations: 0
% 2.39/1.33  #Strategies tried      : 1
% 2.39/1.33  
% 2.39/1.33  Timing (in seconds)
% 2.39/1.33  ----------------------
% 2.39/1.33  Preprocessing        : 0.29
% 2.39/1.33  Parsing              : 0.16
% 2.39/1.33  CNF conversion       : 0.02
% 2.39/1.33  Main loop            : 0.27
% 2.39/1.33  Inferencing          : 0.10
% 2.39/1.33  Reduction            : 0.08
% 2.39/1.33  Demodulation         : 0.05
% 2.39/1.33  BG Simplification    : 0.02
% 2.39/1.33  Subsumption          : 0.06
% 2.39/1.33  Abstraction          : 0.01
% 2.39/1.33  MUC search           : 0.00
% 2.39/1.33  Cooper               : 0.00
% 2.39/1.33  Total                : 0.58
% 2.39/1.33  Index Insertion      : 0.00
% 2.39/1.33  Index Deletion       : 0.00
% 2.39/1.33  Index Matching       : 0.00
% 2.39/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
