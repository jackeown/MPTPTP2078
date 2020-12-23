%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  77 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_60,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_52,B_53] : r1_tarski(k1_tarski(A_52),k2_tarski(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_102,plain,(
    ! [A_16] : r1_tarski(k1_tarski(A_16),k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_99])).

tff(c_105,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    ! [A_16] : k4_xboole_0(k1_tarski(A_16),k1_tarski(A_16)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_105])).

tff(c_54,plain,(
    ! [B_43] : k4_xboole_0(k1_tarski(B_43),k1_tarski(B_43)) != k1_tarski(B_43) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_54])).

tff(c_62,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_121,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_105])).

tff(c_52,plain,(
    ! [A_40,B_41] : r1_tarski(k1_tarski(A_40),k2_tarski(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_323,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_536,plain,(
    ! [A_108,B_109,A_110] :
      ( r1_tarski(A_108,B_109)
      | ~ r1_tarski(A_108,A_110)
      | k4_xboole_0(A_110,B_109) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_323])).

tff(c_649,plain,(
    ! [A_121,B_122,B_123] :
      ( r1_tarski(k1_tarski(A_121),B_122)
      | k4_xboole_0(k2_tarski(A_121,B_123),B_122) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_536])).

tff(c_668,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_649])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_678,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_668,c_4])).

tff(c_48,plain,(
    ! [B_38,C_39] :
      ( k4_xboole_0(k2_tarski(B_38,B_38),C_39) = k1_tarski(B_38)
      | r2_hidden(B_38,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_63,plain,(
    ! [B_38,C_39] :
      ( k4_xboole_0(k1_tarski(B_38),C_39) = k1_tarski(B_38)
      | r2_hidden(B_38,C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_48])).

tff(c_700,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_63])).

tff(c_709,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_700])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( D_15 = B_11
      | D_15 = A_10
      | ~ r2_hidden(D_15,k2_tarski(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_715,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_709,c_14])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.83/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.44  
% 2.83/1.46  tff(f_88, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.83/1.46  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.83/1.46  tff(f_73, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.83/1.46  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.83/1.46  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.83/1.46  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.83/1.46  tff(f_71, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.83/1.46  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.83/1.46  tff(c_60, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.46  tff(c_58, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.46  tff(c_32, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.46  tff(c_99, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), k2_tarski(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.46  tff(c_102, plain, (![A_16]: (r1_tarski(k1_tarski(A_16), k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_99])).
% 2.83/1.46  tff(c_105, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.46  tff(c_119, plain, (![A_16]: (k4_xboole_0(k1_tarski(A_16), k1_tarski(A_16))=k1_xboole_0)), inference(resolution, [status(thm)], [c_102, c_105])).
% 2.83/1.46  tff(c_54, plain, (![B_43]: (k4_xboole_0(k1_tarski(B_43), k1_tarski(B_43))!=k1_tarski(B_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.46  tff(c_138, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_54])).
% 2.83/1.46  tff(c_62, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.46  tff(c_121, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_105])).
% 2.83/1.46  tff(c_52, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), k2_tarski(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.46  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.46  tff(c_323, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.46  tff(c_536, plain, (![A_108, B_109, A_110]: (r1_tarski(A_108, B_109) | ~r1_tarski(A_108, A_110) | k4_xboole_0(A_110, B_109)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_323])).
% 2.83/1.46  tff(c_649, plain, (![A_121, B_122, B_123]: (r1_tarski(k1_tarski(A_121), B_122) | k4_xboole_0(k2_tarski(A_121, B_123), B_122)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_536])).
% 2.83/1.46  tff(c_668, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_649])).
% 2.83/1.46  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.46  tff(c_678, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_668, c_4])).
% 2.83/1.46  tff(c_48, plain, (![B_38, C_39]: (k4_xboole_0(k2_tarski(B_38, B_38), C_39)=k1_tarski(B_38) | r2_hidden(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.83/1.46  tff(c_63, plain, (![B_38, C_39]: (k4_xboole_0(k1_tarski(B_38), C_39)=k1_tarski(B_38) | r2_hidden(B_38, C_39))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_48])).
% 2.83/1.46  tff(c_700, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_678, c_63])).
% 2.83/1.46  tff(c_709, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_138, c_700])).
% 2.83/1.46  tff(c_14, plain, (![D_15, B_11, A_10]: (D_15=B_11 | D_15=A_10 | ~r2_hidden(D_15, k2_tarski(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.46  tff(c_715, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_709, c_14])).
% 2.83/1.46  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_715])).
% 2.83/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.46  
% 2.83/1.46  Inference rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Ref     : 0
% 2.83/1.46  #Sup     : 153
% 2.83/1.46  #Fact    : 0
% 2.83/1.46  #Define  : 0
% 2.83/1.46  #Split   : 0
% 2.83/1.46  #Chain   : 0
% 2.83/1.46  #Close   : 0
% 2.83/1.46  
% 2.83/1.46  Ordering : KBO
% 2.83/1.46  
% 2.83/1.46  Simplification rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Subsume      : 11
% 2.83/1.46  #Demod        : 44
% 2.83/1.46  #Tautology    : 86
% 2.83/1.46  #SimpNegUnit  : 16
% 2.83/1.46  #BackRed      : 0
% 2.83/1.46  
% 2.83/1.46  #Partial instantiations: 0
% 2.83/1.46  #Strategies tried      : 1
% 2.83/1.46  
% 2.83/1.46  Timing (in seconds)
% 2.83/1.46  ----------------------
% 2.94/1.46  Preprocessing        : 0.32
% 2.94/1.46  Parsing              : 0.17
% 2.94/1.46  CNF conversion       : 0.02
% 2.94/1.46  Main loop            : 0.32
% 2.94/1.46  Inferencing          : 0.12
% 2.94/1.46  Reduction            : 0.11
% 2.94/1.46  Demodulation         : 0.08
% 2.94/1.46  BG Simplification    : 0.02
% 2.94/1.46  Subsumption          : 0.06
% 2.94/1.46  Abstraction          : 0.02
% 2.94/1.46  MUC search           : 0.00
% 2.94/1.46  Cooper               : 0.00
% 2.94/1.47  Total                : 0.69
% 2.94/1.47  Index Insertion      : 0.00
% 2.94/1.47  Index Deletion       : 0.00
% 2.94/1.47  Index Matching       : 0.00
% 2.94/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
