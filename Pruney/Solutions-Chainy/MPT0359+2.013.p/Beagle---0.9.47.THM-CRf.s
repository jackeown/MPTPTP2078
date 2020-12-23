%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 138 expanded)
%              Number of equality atoms :   24 (  57 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_16,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,
    ( k2_subset_1('#skF_2') != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_35,plain,
    ( '#skF_2' != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_88,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_35])).

tff(c_32,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | k2_subset_1('#skF_2') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_89,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_34])).

tff(c_90,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_88])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_24])).

tff(c_188,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_192,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_subset_1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_188])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_205,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_12])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_205])).

tff(c_212,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_213,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_216,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    k2_xboole_0(k3_subset_1('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_213,c_216])).

tff(c_238,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_223])).

tff(c_331,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_335,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_331])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_339,plain,
    ( k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_14])).

tff(c_351,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_339])).

tff(c_352,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_351])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_382,plain,(
    ! [C_69,A_70,B_71] :
      ( r2_hidden(C_69,A_70)
      | ~ r2_hidden(C_69,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_399,plain,(
    ! [A_75,B_76,A_77] :
      ( r2_hidden('#skF_1'(A_75,B_76),A_77)
      | ~ m1_subset_1(A_75,k1_zfmisc_1(A_77))
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_8,c_382])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_411,plain,(
    ! [A_78,A_79] :
      ( ~ m1_subset_1(A_78,k1_zfmisc_1(A_79))
      | r1_tarski(A_78,A_79) ) ),
    inference(resolution,[status(thm)],[c_399,c_6])).

tff(c_414,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_411])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > #skF_2 > #skF_3 > #skF_1
% 2.12/1.29  
% 2.12/1.29  %Foreground sorts:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Background operators:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Foreground operators:
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.12/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.29  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.12/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.12/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.29  
% 2.12/1.31  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.12/1.31  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.12/1.31  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.12/1.31  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.12/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.12/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.12/1.31  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.12/1.31  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.12/1.31  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.12/1.31  tff(c_16, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.31  tff(c_26, plain, (k2_subset_1('#skF_2')!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.31  tff(c_35, plain, ('#skF_2'!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26])).
% 2.12/1.31  tff(c_88, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_35])).
% 2.12/1.31  tff(c_32, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | k2_subset_1('#skF_2')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.31  tff(c_34, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.12/1.31  tff(c_89, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_88, c_34])).
% 2.12/1.31  tff(c_90, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_88])).
% 2.12/1.31  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.31  tff(c_91, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_24])).
% 2.12/1.31  tff(c_188, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.31  tff(c_192, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_subset_1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_91, c_188])).
% 2.12/1.31  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.31  tff(c_205, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_192, c_12])).
% 2.12/1.31  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_205])).
% 2.12/1.31  tff(c_212, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_35])).
% 2.12/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.31  tff(c_213, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_35])).
% 2.12/1.31  tff(c_216, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.31  tff(c_223, plain, (k2_xboole_0(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_213, c_216])).
% 2.12/1.31  tff(c_238, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_223])).
% 2.12/1.31  tff(c_331, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.31  tff(c_335, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_331])).
% 2.12/1.31  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.31  tff(c_339, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_14])).
% 2.12/1.31  tff(c_351, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_339])).
% 2.12/1.31  tff(c_352, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_212, c_351])).
% 2.12/1.31  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.31  tff(c_382, plain, (![C_69, A_70, B_71]: (r2_hidden(C_69, A_70) | ~r2_hidden(C_69, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.31  tff(c_399, plain, (![A_75, B_76, A_77]: (r2_hidden('#skF_1'(A_75, B_76), A_77) | ~m1_subset_1(A_75, k1_zfmisc_1(A_77)) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_8, c_382])).
% 2.12/1.31  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.31  tff(c_411, plain, (![A_78, A_79]: (~m1_subset_1(A_78, k1_zfmisc_1(A_79)) | r1_tarski(A_78, A_79))), inference(resolution, [status(thm)], [c_399, c_6])).
% 2.12/1.31  tff(c_414, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_411])).
% 2.12/1.31  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_414])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 91
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 1
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 0
% 2.12/1.31  #Demod        : 26
% 2.12/1.31  #Tautology    : 63
% 2.12/1.31  #SimpNegUnit  : 5
% 2.12/1.31  #BackRed      : 2
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.31  Preprocessing        : 0.28
% 2.12/1.31  Parsing              : 0.15
% 2.12/1.31  CNF conversion       : 0.02
% 2.12/1.31  Main loop            : 0.22
% 2.12/1.31  Inferencing          : 0.09
% 2.12/1.31  Reduction            : 0.07
% 2.12/1.31  Demodulation         : 0.05
% 2.12/1.31  BG Simplification    : 0.01
% 2.12/1.31  Subsumption          : 0.03
% 2.12/1.31  Abstraction          : 0.01
% 2.12/1.31  MUC search           : 0.00
% 2.12/1.31  Cooper               : 0.00
% 2.12/1.31  Total                : 0.54
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
