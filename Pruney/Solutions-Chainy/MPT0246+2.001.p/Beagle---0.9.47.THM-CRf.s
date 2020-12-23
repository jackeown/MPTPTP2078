%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 154 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  109 ( 316 expanded)
%              Number of equality atoms :   31 ( 104 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    k1_tarski('#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),A_50)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [C_33] :
      ( C_33 = '#skF_3'
      | ~ r2_hidden(C_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_67,plain,(
    ! [B_52] :
      ( '#skF_1'('#skF_2',B_52) = '#skF_3'
      | r1_tarski('#skF_2',B_52) ) ),
    inference(resolution,[status(thm)],[c_61,c_34])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [B_11] :
      ( k1_xboole_0 = '#skF_2'
      | '#skF_1'('#skF_2',k4_xboole_0(B_11,'#skF_2')) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_67,c_16])).

tff(c_75,plain,(
    ! [B_53] : '#skF_1'('#skF_2',k4_xboole_0(B_53,'#skF_2')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_71])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_3','#skF_2')
      | r1_tarski('#skF_2',k4_xboole_0(B_53,'#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_8])).

tff(c_132,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    ! [B_51] :
      ( '#skF_1'('#skF_2',B_51) = '#skF_3'
      | r1_tarski('#skF_2',B_51) ) ),
    inference(resolution,[status(thm)],[c_61,c_34])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_xboole_0(A_8,B_9)
      | B_9 = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_103,plain,(
    ! [A_57,B_58] :
      ( r2_xboole_0(A_57,B_58)
      | B_58 = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_xboole_0(B_2,A_1)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_139,plain,(
    ! [B_63,A_64] :
      ( ~ r2_xboole_0(B_63,A_64)
      | B_63 = A_64
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_144,plain,(
    ! [B_65,A_66] :
      ( ~ r1_tarski(B_65,A_66)
      | B_65 = A_66
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_213,plain,(
    ! [B_78] :
      ( B_78 = '#skF_2'
      | ~ r1_tarski(B_78,'#skF_2')
      | '#skF_1'('#skF_2',B_78) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_66,c_144])).

tff(c_230,plain,(
    ! [A_30] :
      ( k1_tarski(A_30) = '#skF_2'
      | '#skF_1'('#skF_2',k1_tarski(A_30)) = '#skF_3'
      | ~ r2_hidden(A_30,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_213])).

tff(c_117,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden('#skF_1'(A_59,B_60),B_60)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [A_61] : r1_tarski(A_61,A_61) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | ~ r1_tarski(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(resolution,[status(thm)],[c_126,c_30])).

tff(c_160,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_358,plain,(
    ! [A_101,B_102,B_103] :
      ( r2_hidden('#skF_1'(A_101,B_102),B_103)
      | ~ r1_tarski(A_101,B_103)
      | r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_443,plain,(
    ! [A_113,B_114] :
      ( '#skF_1'(A_113,B_114) = '#skF_3'
      | ~ r1_tarski(A_113,'#skF_2')
      | r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_358,c_34])).

tff(c_540,plain,(
    ! [A_122,B_123] :
      ( '#skF_1'(k1_tarski(A_122),B_123) = '#skF_3'
      | r1_tarski(k1_tarski(A_122),B_123)
      | ~ r2_hidden(A_122,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_443])).

tff(c_573,plain,(
    ! [A_124,B_125] :
      ( r2_hidden(A_124,B_125)
      | '#skF_1'(k1_tarski(A_124),B_125) = '#skF_3'
      | ~ r2_hidden(A_124,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_540,c_30])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_703,plain,(
    ! [B_134,A_135] :
      ( ~ r2_hidden('#skF_3',B_134)
      | r1_tarski(k1_tarski(A_135),B_134)
      | r2_hidden(A_135,B_134)
      | ~ r2_hidden(A_135,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_6])).

tff(c_740,plain,(
    ! [B_136,A_137] :
      ( ~ r2_hidden('#skF_3',B_136)
      | r2_hidden(A_137,B_136)
      | ~ r2_hidden(A_137,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_703,c_30])).

tff(c_764,plain,(
    ! [A_138] :
      ( r2_hidden(A_138,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_138,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_740])).

tff(c_836,plain,(
    ! [A_143] :
      ( r1_tarski(A_143,k1_tarski('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_143,k1_tarski('#skF_3')),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_764,c_6])).

tff(c_844,plain,
    ( r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_3','#skF_2')
    | k1_tarski('#skF_3') = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_836])).

tff(c_856,plain,
    ( r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | k1_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_844])).

tff(c_857,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_856])).

tff(c_158,plain,(
    ! [A_30,B_31] :
      ( k1_tarski(A_30) = B_31
      | ~ r1_tarski(B_31,k1_tarski(A_30))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_144])).

tff(c_866,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_857,c_158])).

tff(c_876,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_866])).

tff(c_878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_876])).

tff(c_882,plain,(
    ! [B_145] : r1_tarski('#skF_2',k4_xboole_0(B_145,'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_885,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_882,c_16])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.49  
% 3.08/1.49  %Foreground sorts:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Background operators:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Foreground operators:
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.08/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.08/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.49  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.49  
% 3.08/1.50  tff(f_79, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.08/1.50  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.08/1.50  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.08/1.50  tff(f_64, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.08/1.50  tff(f_44, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.08/1.50  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 3.08/1.50  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_38, plain, (k1_tarski('#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_61, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), A_50) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.50  tff(c_34, plain, (![C_33]: (C_33='#skF_3' | ~r2_hidden(C_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_67, plain, (![B_52]: ('#skF_1'('#skF_2', B_52)='#skF_3' | r1_tarski('#skF_2', B_52))), inference(resolution, [status(thm)], [c_61, c_34])).
% 3.08/1.50  tff(c_16, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k4_xboole_0(B_11, A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.50  tff(c_71, plain, (![B_11]: (k1_xboole_0='#skF_2' | '#skF_1'('#skF_2', k4_xboole_0(B_11, '#skF_2'))='#skF_3')), inference(resolution, [status(thm)], [c_67, c_16])).
% 3.08/1.50  tff(c_75, plain, (![B_53]: ('#skF_1'('#skF_2', k4_xboole_0(B_53, '#skF_2'))='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_71])).
% 3.08/1.50  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.50  tff(c_80, plain, (![B_53]: (r2_hidden('#skF_3', '#skF_2') | r1_tarski('#skF_2', k4_xboole_0(B_53, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_75, c_8])).
% 3.08/1.50  tff(c_132, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_80])).
% 3.08/1.50  tff(c_32, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.08/1.50  tff(c_66, plain, (![B_51]: ('#skF_1'('#skF_2', B_51)='#skF_3' | r1_tarski('#skF_2', B_51))), inference(resolution, [status(thm)], [c_61, c_34])).
% 3.08/1.50  tff(c_10, plain, (![A_8, B_9]: (r2_xboole_0(A_8, B_9) | B_9=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.50  tff(c_103, plain, (![A_57, B_58]: (r2_xboole_0(A_57, B_58) | B_58=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.50  tff(c_2, plain, (![B_2, A_1]: (~r2_xboole_0(B_2, A_1) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.08/1.50  tff(c_139, plain, (![B_63, A_64]: (~r2_xboole_0(B_63, A_64) | B_63=A_64 | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_103, c_2])).
% 3.08/1.50  tff(c_144, plain, (![B_65, A_66]: (~r1_tarski(B_65, A_66) | B_65=A_66 | ~r1_tarski(A_66, B_65))), inference(resolution, [status(thm)], [c_10, c_139])).
% 3.08/1.50  tff(c_213, plain, (![B_78]: (B_78='#skF_2' | ~r1_tarski(B_78, '#skF_2') | '#skF_1'('#skF_2', B_78)='#skF_3')), inference(resolution, [status(thm)], [c_66, c_144])).
% 3.08/1.50  tff(c_230, plain, (![A_30]: (k1_tarski(A_30)='#skF_2' | '#skF_1'('#skF_2', k1_tarski(A_30))='#skF_3' | ~r2_hidden(A_30, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_213])).
% 3.08/1.50  tff(c_117, plain, (![A_59, B_60]: (~r2_hidden('#skF_1'(A_59, B_60), B_60) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.50  tff(c_126, plain, (![A_61]: (r1_tarski(A_61, A_61))), inference(resolution, [status(thm)], [c_8, c_117])).
% 3.08/1.50  tff(c_30, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | ~r1_tarski(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.08/1.50  tff(c_131, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(resolution, [status(thm)], [c_126, c_30])).
% 3.08/1.50  tff(c_160, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.50  tff(c_358, plain, (![A_101, B_102, B_103]: (r2_hidden('#skF_1'(A_101, B_102), B_103) | ~r1_tarski(A_101, B_103) | r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_8, c_160])).
% 3.08/1.50  tff(c_443, plain, (![A_113, B_114]: ('#skF_1'(A_113, B_114)='#skF_3' | ~r1_tarski(A_113, '#skF_2') | r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_358, c_34])).
% 3.08/1.50  tff(c_540, plain, (![A_122, B_123]: ('#skF_1'(k1_tarski(A_122), B_123)='#skF_3' | r1_tarski(k1_tarski(A_122), B_123) | ~r2_hidden(A_122, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_443])).
% 3.08/1.50  tff(c_573, plain, (![A_124, B_125]: (r2_hidden(A_124, B_125) | '#skF_1'(k1_tarski(A_124), B_125)='#skF_3' | ~r2_hidden(A_124, '#skF_2'))), inference(resolution, [status(thm)], [c_540, c_30])).
% 3.08/1.50  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.50  tff(c_703, plain, (![B_134, A_135]: (~r2_hidden('#skF_3', B_134) | r1_tarski(k1_tarski(A_135), B_134) | r2_hidden(A_135, B_134) | ~r2_hidden(A_135, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_6])).
% 3.08/1.50  tff(c_740, plain, (![B_136, A_137]: (~r2_hidden('#skF_3', B_136) | r2_hidden(A_137, B_136) | ~r2_hidden(A_137, '#skF_2'))), inference(resolution, [status(thm)], [c_703, c_30])).
% 3.08/1.50  tff(c_764, plain, (![A_138]: (r2_hidden(A_138, k1_tarski('#skF_3')) | ~r2_hidden(A_138, '#skF_2'))), inference(resolution, [status(thm)], [c_131, c_740])).
% 3.08/1.50  tff(c_836, plain, (![A_143]: (r1_tarski(A_143, k1_tarski('#skF_3')) | ~r2_hidden('#skF_1'(A_143, k1_tarski('#skF_3')), '#skF_2'))), inference(resolution, [status(thm)], [c_764, c_6])).
% 3.08/1.50  tff(c_844, plain, (r1_tarski('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden('#skF_3', '#skF_2') | k1_tarski('#skF_3')='#skF_2' | ~r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_230, c_836])).
% 3.08/1.50  tff(c_856, plain, (r1_tarski('#skF_2', k1_tarski('#skF_3')) | k1_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_844])).
% 3.08/1.50  tff(c_857, plain, (r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_856])).
% 3.08/1.50  tff(c_158, plain, (![A_30, B_31]: (k1_tarski(A_30)=B_31 | ~r1_tarski(B_31, k1_tarski(A_30)) | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_32, c_144])).
% 3.08/1.50  tff(c_866, plain, (k1_tarski('#skF_3')='#skF_2' | ~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_857, c_158])).
% 3.08/1.50  tff(c_876, plain, (k1_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_866])).
% 3.08/1.50  tff(c_878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_876])).
% 3.08/1.50  tff(c_882, plain, (![B_145]: (r1_tarski('#skF_2', k4_xboole_0(B_145, '#skF_2')))), inference(splitRight, [status(thm)], [c_80])).
% 3.08/1.50  tff(c_885, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_882, c_16])).
% 3.08/1.50  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_885])).
% 3.08/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.50  
% 3.08/1.50  Inference rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Ref     : 0
% 3.08/1.50  #Sup     : 192
% 3.08/1.50  #Fact    : 0
% 3.08/1.50  #Define  : 0
% 3.08/1.50  #Split   : 2
% 3.08/1.50  #Chain   : 0
% 3.08/1.50  #Close   : 0
% 3.08/1.50  
% 3.08/1.50  Ordering : KBO
% 3.08/1.50  
% 3.08/1.50  Simplification rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Subsume      : 37
% 3.08/1.50  #Demod        : 42
% 3.08/1.50  #Tautology    : 69
% 3.08/1.50  #SimpNegUnit  : 8
% 3.08/1.50  #BackRed      : 0
% 3.08/1.50  
% 3.08/1.50  #Partial instantiations: 0
% 3.08/1.50  #Strategies tried      : 1
% 3.08/1.51  
% 3.08/1.51  Timing (in seconds)
% 3.08/1.51  ----------------------
% 3.08/1.51  Preprocessing        : 0.30
% 3.26/1.51  Parsing              : 0.16
% 3.26/1.51  CNF conversion       : 0.02
% 3.26/1.51  Main loop            : 0.43
% 3.26/1.51  Inferencing          : 0.16
% 3.26/1.51  Reduction            : 0.12
% 3.26/1.51  Demodulation         : 0.08
% 3.26/1.51  BG Simplification    : 0.02
% 3.26/1.51  Subsumption          : 0.10
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.51  MUC search           : 0.00
% 3.26/1.51  Cooper               : 0.00
% 3.26/1.51  Total                : 0.77
% 3.26/1.51  Index Insertion      : 0.00
% 3.26/1.51  Index Deletion       : 0.00
% 3.26/1.51  Index Matching       : 0.00
% 3.26/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
