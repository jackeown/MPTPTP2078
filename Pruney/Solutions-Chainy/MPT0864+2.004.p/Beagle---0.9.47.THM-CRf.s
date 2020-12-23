%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 132 expanded)
%              Number of equality atoms :   40 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_78,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,(
    ! [A_36,B_37] : k1_mcart_1(k4_tarski(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_87,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_78])).

tff(c_103,plain,(
    ! [A_39,B_40] : k2_mcart_1(k4_tarski(A_39,B_40)) = B_40 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_112,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_103])).

tff(c_58,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_119,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_112,c_58])).

tff(c_120,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_122,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60])).

tff(c_346,plain,(
    ! [A_97,B_98] : k2_zfmisc_1(k1_tarski(A_97),k1_tarski(B_98)) = k1_tarski(k4_tarski(A_97,B_98)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(A_16,k2_zfmisc_1(A_16,B_17))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_396,plain,(
    ! [A_110,B_111] :
      ( ~ r1_tarski(k1_tarski(A_110),k1_tarski(k4_tarski(A_110,B_111)))
      | k1_tarski(A_110) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_22])).

tff(c_399,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1'))
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_396])).

tff(c_401,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_399])).

tff(c_44,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_tarski(A_24)) = k1_ordinal1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_441,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k1_ordinal1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_44])).

tff(c_456,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_441])).

tff(c_48,plain,(
    ! [B_26] : r2_hidden(B_26,k1_ordinal1(B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_143,plain,(
    ! [B_41,A_42] :
      ( ~ r1_tarski(B_41,A_42)
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_147,plain,(
    ! [B_26] : ~ r1_tarski(k1_ordinal1(B_26),B_26) ),
    inference(resolution,[status(thm)],[c_48,c_143])).

tff(c_488,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_147])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_488])).

tff(c_502,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_505,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_60])).

tff(c_739,plain,(
    ! [A_170,B_171] : k2_zfmisc_1(k1_tarski(A_170),k1_tarski(B_171)) = k1_tarski(k4_tarski(A_170,B_171)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(A_16,k2_zfmisc_1(B_17,A_16))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_825,plain,(
    ! [B_185,A_186] :
      ( ~ r1_tarski(k1_tarski(B_185),k1_tarski(k4_tarski(A_186,B_185)))
      | k1_tarski(B_185) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_20])).

tff(c_828,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1'))
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_825])).

tff(c_830,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_828])).

tff(c_870,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k1_ordinal1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_44])).

tff(c_885,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_870])).

tff(c_536,plain,(
    ! [B_116,A_117] :
      ( ~ r1_tarski(B_116,A_117)
      | ~ r2_hidden(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_540,plain,(
    ! [B_26] : ~ r1_tarski(k1_ordinal1(B_26),B_26) ),
    inference(resolution,[status(thm)],[c_48,c_536])).

tff(c_917,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_540])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_917])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.50  
% 2.91/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.50  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.91/1.50  
% 2.91/1.50  %Foreground sorts:
% 2.91/1.50  
% 2.91/1.50  
% 2.91/1.50  %Background operators:
% 2.91/1.50  
% 2.91/1.50  
% 2.91/1.50  %Foreground operators:
% 2.91/1.50  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.91/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.91/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.91/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.91/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.91/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.50  
% 2.91/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.91/1.52  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.91/1.52  tff(f_105, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.91/1.52  tff(f_95, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.91/1.52  tff(f_78, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.91/1.52  tff(f_49, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.91/1.52  tff(f_80, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.91/1.52  tff(f_86, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.91/1.52  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.91/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.52  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.91/1.52  tff(c_60, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.91/1.52  tff(c_78, plain, (![A_36, B_37]: (k1_mcart_1(k4_tarski(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.91/1.52  tff(c_87, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_60, c_78])).
% 2.91/1.52  tff(c_103, plain, (![A_39, B_40]: (k2_mcart_1(k4_tarski(A_39, B_40))=B_40)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.91/1.52  tff(c_112, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_60, c_103])).
% 2.91/1.52  tff(c_58, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.91/1.52  tff(c_119, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_112, c_58])).
% 2.91/1.52  tff(c_120, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_119])).
% 2.91/1.52  tff(c_122, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60])).
% 2.91/1.52  tff(c_346, plain, (![A_97, B_98]: (k2_zfmisc_1(k1_tarski(A_97), k1_tarski(B_98))=k1_tarski(k4_tarski(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.91/1.52  tff(c_22, plain, (![A_16, B_17]: (~r1_tarski(A_16, k2_zfmisc_1(A_16, B_17)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.52  tff(c_396, plain, (![A_110, B_111]: (~r1_tarski(k1_tarski(A_110), k1_tarski(k4_tarski(A_110, B_111))) | k1_tarski(A_110)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_346, c_22])).
% 2.91/1.52  tff(c_399, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1')) | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122, c_396])).
% 2.91/1.52  tff(c_401, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_399])).
% 2.91/1.52  tff(c_44, plain, (![A_24]: (k2_xboole_0(A_24, k1_tarski(A_24))=k1_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.91/1.52  tff(c_441, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k1_ordinal1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_401, c_44])).
% 2.91/1.52  tff(c_456, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_441])).
% 2.91/1.52  tff(c_48, plain, (![B_26]: (r2_hidden(B_26, k1_ordinal1(B_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.91/1.52  tff(c_143, plain, (![B_41, A_42]: (~r1_tarski(B_41, A_42) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.91/1.52  tff(c_147, plain, (![B_26]: (~r1_tarski(k1_ordinal1(B_26), B_26))), inference(resolution, [status(thm)], [c_48, c_143])).
% 2.91/1.52  tff(c_488, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_456, c_147])).
% 2.91/1.52  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_488])).
% 2.91/1.52  tff(c_502, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_119])).
% 2.91/1.52  tff(c_505, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_502, c_60])).
% 2.91/1.52  tff(c_739, plain, (![A_170, B_171]: (k2_zfmisc_1(k1_tarski(A_170), k1_tarski(B_171))=k1_tarski(k4_tarski(A_170, B_171)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.91/1.52  tff(c_20, plain, (![A_16, B_17]: (~r1_tarski(A_16, k2_zfmisc_1(B_17, A_16)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.52  tff(c_825, plain, (![B_185, A_186]: (~r1_tarski(k1_tarski(B_185), k1_tarski(k4_tarski(A_186, B_185))) | k1_tarski(B_185)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_739, c_20])).
% 2.91/1.52  tff(c_828, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1')) | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_505, c_825])).
% 2.91/1.52  tff(c_830, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_828])).
% 2.91/1.52  tff(c_870, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k1_ordinal1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_830, c_44])).
% 2.91/1.52  tff(c_885, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_870])).
% 2.91/1.52  tff(c_536, plain, (![B_116, A_117]: (~r1_tarski(B_116, A_117) | ~r2_hidden(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.91/1.52  tff(c_540, plain, (![B_26]: (~r1_tarski(k1_ordinal1(B_26), B_26))), inference(resolution, [status(thm)], [c_48, c_536])).
% 2.91/1.52  tff(c_917, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_885, c_540])).
% 2.91/1.52  tff(c_930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_917])).
% 2.91/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.52  
% 2.91/1.52  Inference rules
% 2.91/1.52  ----------------------
% 2.91/1.52  #Ref     : 0
% 2.91/1.52  #Sup     : 213
% 2.91/1.52  #Fact    : 0
% 2.91/1.52  #Define  : 0
% 2.91/1.52  #Split   : 3
% 2.91/1.52  #Chain   : 0
% 2.91/1.52  #Close   : 0
% 2.91/1.52  
% 2.91/1.52  Ordering : KBO
% 2.91/1.52  
% 2.91/1.52  Simplification rules
% 2.91/1.52  ----------------------
% 2.91/1.52  #Subsume      : 4
% 2.91/1.52  #Demod        : 100
% 2.91/1.52  #Tautology    : 124
% 2.91/1.52  #SimpNegUnit  : 0
% 2.91/1.52  #BackRed      : 6
% 2.91/1.52  
% 2.91/1.52  #Partial instantiations: 0
% 2.91/1.52  #Strategies tried      : 1
% 2.91/1.52  
% 2.91/1.52  Timing (in seconds)
% 2.91/1.52  ----------------------
% 2.91/1.52  Preprocessing        : 0.34
% 2.91/1.52  Parsing              : 0.18
% 2.91/1.52  CNF conversion       : 0.02
% 2.91/1.52  Main loop            : 0.36
% 2.91/1.52  Inferencing          : 0.13
% 2.91/1.52  Reduction            : 0.12
% 2.91/1.52  Demodulation         : 0.09
% 2.91/1.52  BG Simplification    : 0.02
% 2.91/1.52  Subsumption          : 0.06
% 2.91/1.52  Abstraction          : 0.02
% 2.91/1.52  MUC search           : 0.00
% 2.91/1.52  Cooper               : 0.00
% 2.91/1.52  Total                : 0.73
% 2.91/1.52  Index Insertion      : 0.00
% 2.91/1.52  Index Deletion       : 0.00
% 2.91/1.52  Index Matching       : 0.00
% 2.91/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
