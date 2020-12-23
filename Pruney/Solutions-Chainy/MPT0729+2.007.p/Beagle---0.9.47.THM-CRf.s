%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:58 EST 2020

% Result     : Theorem 14.77s
% Output     : CNFRefutation 14.77s
% Verified   : 
% Statistics : Number of formulae       :   61 (  88 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 139 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_68,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_23] : r2_hidden(A_23,k1_ordinal1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    k1_ordinal1('#skF_5') = k1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_tarski(A_22)) = k1_ordinal1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_220,plain,(
    ! [B_67,A_68] :
      ( k4_xboole_0(k2_xboole_0(B_67,k1_tarski(A_68)),k1_tarski(A_68)) = B_67
      | r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_243,plain,(
    ! [A_69] :
      ( k4_xboole_0(k1_ordinal1(A_69),k1_tarski(A_69)) = A_69
      | r2_hidden(A_69,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_220])).

tff(c_258,plain,
    ( k4_xboole_0(k1_ordinal1('#skF_6'),k1_tarski('#skF_5')) = '#skF_5'
    | r2_hidden('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_243])).

tff(c_261,plain,(
    r2_hidden('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_56,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_264,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_261,c_56])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_264])).

tff(c_271,plain,(
    k4_xboole_0(k1_ordinal1('#skF_6'),k1_tarski('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_424,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,'#skF_5')
      | r2_hidden(D_85,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_85,k1_ordinal1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_4])).

tff(c_46,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_200,plain,(
    ! [D_62,B_63,A_64] :
      ( D_62 = B_63
      | D_62 = A_64
      | ~ r2_hidden(D_62,k2_tarski(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_203,plain,(
    ! [D_62,A_17] :
      ( D_62 = A_17
      | D_62 = A_17
      | ~ r2_hidden(D_62,k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_200])).

tff(c_474,plain,(
    ! [D_86] :
      ( D_86 = '#skF_5'
      | r2_hidden(D_86,'#skF_5')
      | ~ r2_hidden(D_86,k1_ordinal1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_424,c_203])).

tff(c_484,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_474])).

tff(c_492,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_484])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_499,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_492,c_2])).

tff(c_67,plain,(
    ! [A_27] : r2_hidden(A_27,k1_ordinal1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_67])).

tff(c_50,plain,(
    ! [B_21,A_20] :
      ( k4_xboole_0(k2_xboole_0(B_21,k1_tarski(A_20)),k1_tarski(A_20)) = B_21
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_273,plain,(
    ! [D_70,A_71,B_72] :
      ( r2_hidden(D_70,k4_xboole_0(A_71,B_72))
      | r2_hidden(D_70,B_72)
      | ~ r2_hidden(D_70,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5064,plain,(
    ! [D_286,B_287,A_288] :
      ( r2_hidden(D_286,B_287)
      | r2_hidden(D_286,k1_tarski(A_288))
      | ~ r2_hidden(D_286,k2_xboole_0(B_287,k1_tarski(A_288)))
      | r2_hidden(A_288,B_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_273])).

tff(c_28197,plain,(
    ! [D_790,A_791] :
      ( r2_hidden(D_790,A_791)
      | r2_hidden(D_790,k1_tarski(A_791))
      | ~ r2_hidden(D_790,k1_ordinal1(A_791))
      | r2_hidden(A_791,A_791) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_5064])).

tff(c_29058,plain,(
    ! [A_791,D_790] :
      ( ~ r1_tarski(A_791,A_791)
      | r2_hidden(D_790,A_791)
      | r2_hidden(D_790,k1_tarski(A_791))
      | ~ r2_hidden(D_790,k1_ordinal1(A_791)) ) ),
    inference(resolution,[status(thm)],[c_28197,c_56])).

tff(c_29342,plain,(
    ! [D_792,A_793] :
      ( r2_hidden(D_792,A_793)
      | r2_hidden(D_792,k1_tarski(A_793))
      | ~ r2_hidden(D_792,k1_ordinal1(A_793)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_29058])).

tff(c_30134,plain,(
    ! [D_794,A_795] :
      ( D_794 = A_795
      | r2_hidden(D_794,A_795)
      | ~ r2_hidden(D_794,k1_ordinal1(A_795)) ) ),
    inference(resolution,[status(thm)],[c_29342,c_203])).

tff(c_30232,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_30134])).

tff(c_30267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_58,c_30232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.77/7.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.77/7.29  
% 14.77/7.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.77/7.29  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 14.77/7.29  
% 14.77/7.29  %Foreground sorts:
% 14.77/7.29  
% 14.77/7.29  
% 14.77/7.29  %Background operators:
% 14.77/7.29  
% 14.77/7.29  
% 14.77/7.29  %Foreground operators:
% 14.77/7.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.77/7.29  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 14.77/7.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.77/7.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.77/7.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.77/7.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.77/7.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.77/7.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.77/7.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.77/7.29  tff('#skF_5', type, '#skF_5': $i).
% 14.77/7.29  tff('#skF_6', type, '#skF_6': $i).
% 14.77/7.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.77/7.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.77/7.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.77/7.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.77/7.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.77/7.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.77/7.29  
% 14.77/7.30  tff(f_78, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 14.77/7.30  tff(f_68, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 14.77/7.30  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.77/7.30  tff(f_66, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 14.77/7.30  tff(f_64, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 14.77/7.30  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 14.77/7.30  tff(f_40, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.77/7.30  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 14.77/7.30  tff(f_55, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 14.77/7.30  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 14.77/7.30  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.77/7.30  tff(c_54, plain, (![A_23]: (r2_hidden(A_23, k1_ordinal1(A_23)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.77/7.30  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.77/7.30  tff(c_60, plain, (k1_ordinal1('#skF_5')=k1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.77/7.30  tff(c_52, plain, (![A_22]: (k2_xboole_0(A_22, k1_tarski(A_22))=k1_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.77/7.31  tff(c_220, plain, (![B_67, A_68]: (k4_xboole_0(k2_xboole_0(B_67, k1_tarski(A_68)), k1_tarski(A_68))=B_67 | r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.77/7.31  tff(c_243, plain, (![A_69]: (k4_xboole_0(k1_ordinal1(A_69), k1_tarski(A_69))=A_69 | r2_hidden(A_69, A_69))), inference(superposition, [status(thm), theory('equality')], [c_52, c_220])).
% 14.77/7.31  tff(c_258, plain, (k4_xboole_0(k1_ordinal1('#skF_6'), k1_tarski('#skF_5'))='#skF_5' | r2_hidden('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_243])).
% 14.77/7.31  tff(c_261, plain, (r2_hidden('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_258])).
% 14.77/7.31  tff(c_56, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.77/7.31  tff(c_264, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_261, c_56])).
% 14.77/7.31  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_264])).
% 14.77/7.31  tff(c_271, plain, (k4_xboole_0(k1_ordinal1('#skF_6'), k1_tarski('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_258])).
% 14.77/7.31  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.77/7.31  tff(c_424, plain, (![D_85]: (r2_hidden(D_85, '#skF_5') | r2_hidden(D_85, k1_tarski('#skF_5')) | ~r2_hidden(D_85, k1_ordinal1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_271, c_4])).
% 14.77/7.31  tff(c_46, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.77/7.31  tff(c_200, plain, (![D_62, B_63, A_64]: (D_62=B_63 | D_62=A_64 | ~r2_hidden(D_62, k2_tarski(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.77/7.31  tff(c_203, plain, (![D_62, A_17]: (D_62=A_17 | D_62=A_17 | ~r2_hidden(D_62, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_200])).
% 14.77/7.31  tff(c_474, plain, (![D_86]: (D_86='#skF_5' | r2_hidden(D_86, '#skF_5') | ~r2_hidden(D_86, k1_ordinal1('#skF_6')))), inference(resolution, [status(thm)], [c_424, c_203])).
% 14.77/7.31  tff(c_484, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_474])).
% 14.77/7.31  tff(c_492, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_484])).
% 14.77/7.31  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 14.77/7.31  tff(c_499, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_492, c_2])).
% 14.77/7.31  tff(c_67, plain, (![A_27]: (r2_hidden(A_27, k1_ordinal1(A_27)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.77/7.31  tff(c_70, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_67])).
% 14.77/7.31  tff(c_50, plain, (![B_21, A_20]: (k4_xboole_0(k2_xboole_0(B_21, k1_tarski(A_20)), k1_tarski(A_20))=B_21 | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.77/7.31  tff(c_273, plain, (![D_70, A_71, B_72]: (r2_hidden(D_70, k4_xboole_0(A_71, B_72)) | r2_hidden(D_70, B_72) | ~r2_hidden(D_70, A_71))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.77/7.31  tff(c_5064, plain, (![D_286, B_287, A_288]: (r2_hidden(D_286, B_287) | r2_hidden(D_286, k1_tarski(A_288)) | ~r2_hidden(D_286, k2_xboole_0(B_287, k1_tarski(A_288))) | r2_hidden(A_288, B_287))), inference(superposition, [status(thm), theory('equality')], [c_50, c_273])).
% 14.77/7.31  tff(c_28197, plain, (![D_790, A_791]: (r2_hidden(D_790, A_791) | r2_hidden(D_790, k1_tarski(A_791)) | ~r2_hidden(D_790, k1_ordinal1(A_791)) | r2_hidden(A_791, A_791))), inference(superposition, [status(thm), theory('equality')], [c_52, c_5064])).
% 14.77/7.31  tff(c_29058, plain, (![A_791, D_790]: (~r1_tarski(A_791, A_791) | r2_hidden(D_790, A_791) | r2_hidden(D_790, k1_tarski(A_791)) | ~r2_hidden(D_790, k1_ordinal1(A_791)))), inference(resolution, [status(thm)], [c_28197, c_56])).
% 14.77/7.31  tff(c_29342, plain, (![D_792, A_793]: (r2_hidden(D_792, A_793) | r2_hidden(D_792, k1_tarski(A_793)) | ~r2_hidden(D_792, k1_ordinal1(A_793)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_29058])).
% 14.77/7.31  tff(c_30134, plain, (![D_794, A_795]: (D_794=A_795 | r2_hidden(D_794, A_795) | ~r2_hidden(D_794, k1_ordinal1(A_795)))), inference(resolution, [status(thm)], [c_29342, c_203])).
% 14.77/7.31  tff(c_30232, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_30134])).
% 14.77/7.31  tff(c_30267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_58, c_30232])).
% 14.77/7.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.77/7.31  
% 14.77/7.31  Inference rules
% 14.77/7.31  ----------------------
% 14.77/7.31  #Ref     : 0
% 14.77/7.31  #Sup     : 6519
% 14.77/7.31  #Fact    : 4
% 14.77/7.31  #Define  : 0
% 14.77/7.31  #Split   : 14
% 14.77/7.31  #Chain   : 0
% 14.77/7.31  #Close   : 0
% 14.77/7.31  
% 14.77/7.31  Ordering : KBO
% 14.77/7.31  
% 14.77/7.31  Simplification rules
% 14.77/7.31  ----------------------
% 14.77/7.31  #Subsume      : 1724
% 14.77/7.31  #Demod        : 1131
% 14.77/7.31  #Tautology    : 262
% 14.77/7.31  #SimpNegUnit  : 399
% 14.77/7.31  #BackRed      : 0
% 14.77/7.31  
% 14.77/7.31  #Partial instantiations: 0
% 14.77/7.31  #Strategies tried      : 1
% 14.77/7.31  
% 14.77/7.31  Timing (in seconds)
% 14.77/7.31  ----------------------
% 14.77/7.31  Preprocessing        : 0.31
% 14.77/7.31  Parsing              : 0.15
% 14.77/7.31  CNF conversion       : 0.02
% 14.77/7.31  Main loop            : 6.23
% 14.77/7.31  Inferencing          : 1.00
% 14.77/7.31  Reduction            : 1.83
% 14.77/7.31  Demodulation         : 0.84
% 14.77/7.31  BG Simplification    : 0.13
% 14.77/7.31  Subsumption          : 2.90
% 14.77/7.31  Abstraction          : 0.17
% 14.77/7.31  MUC search           : 0.00
% 14.77/7.31  Cooper               : 0.00
% 14.77/7.31  Total                : 6.57
% 14.77/7.31  Index Insertion      : 0.00
% 14.77/7.31  Index Deletion       : 0.00
% 14.77/7.31  Index Matching       : 0.00
% 14.77/7.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
