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
% DateTime   : Thu Dec  3 09:45:19 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 166 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(c_2084,plain,(
    ! [A_99,B_100] :
      ( r1_xboole_0(A_99,B_100)
      | k4_xboole_0(A_99,B_100) != A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2096,plain,(
    ! [B_101,A_102] :
      ( r1_xboole_0(B_101,A_102)
      | k4_xboole_0(A_102,B_101) != A_102 ) ),
    inference(resolution,[status(thm)],[c_2084,c_2])).

tff(c_168,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_176,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_168,c_29])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_193,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_242,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_193])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_232,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_193])).

tff(c_245,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_232])).

tff(c_388,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_422,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_388])).

tff(c_433,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_68,c_422])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_xboole_0(A_12,k4_xboole_0(B_13,C_14))
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_514,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,k4_xboole_0(B_56,C_57))
      | ~ r1_xboole_0(A_55,C_57)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_547,plain,(
    ! [A_55] :
      ( ~ r1_xboole_0(A_55,k1_xboole_0)
      | ~ r1_xboole_0(A_55,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_55,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_514])).

tff(c_714,plain,(
    ! [A_64] :
      ( ~ r1_xboole_0(A_64,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_64,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_547])).

tff(c_949,plain,(
    ! [A_67] :
      ( r1_xboole_0(A_67,'#skF_1')
      | ~ r1_xboole_0(A_67,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_714])).

tff(c_983,plain,(
    ! [A_68] : r1_xboole_0(k4_xboole_0(A_68,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_949])).

tff(c_1013,plain,(
    ! [A_69] : r1_xboole_0('#skF_1',k4_xboole_0(A_69,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_983,c_2])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1820,plain,(
    ! [A_83] : k4_xboole_0('#skF_1',k4_xboole_0(A_83,'#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1013,c_18])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1853,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1910,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1853,c_8])).

tff(c_1916,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_242,c_1910])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_1916])).

tff(c_1919,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2107,plain,(
    k4_xboole_0('#skF_3','#skF_1') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2096,c_1919])).

tff(c_1921,plain,(
    ! [B_84,A_85] :
      ( r1_xboole_0(B_84,A_85)
      | ~ r1_xboole_0(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1926,plain,(
    ! [B_11,A_10] : r1_xboole_0(B_11,k4_xboole_0(A_10,B_11)) ),
    inference(resolution,[status(thm)],[c_14,c_1921])).

tff(c_1972,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1980,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1972])).

tff(c_2543,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ r1_xboole_0(A_118,k4_xboole_0(B_119,C_120))
      | ~ r1_xboole_0(A_118,C_120)
      | r1_xboole_0(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2579,plain,(
    ! [A_118] :
      ( ~ r1_xboole_0(A_118,k1_xboole_0)
      | ~ r1_xboole_0(A_118,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_118,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_2543])).

tff(c_2672,plain,(
    ! [A_123] :
      ( ~ r1_xboole_0(A_123,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_123,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2579])).

tff(c_2705,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1926,c_2672])).

tff(c_2711,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2705,c_18])).

tff(c_2717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2107,c_2711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.66  
% 3.88/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.66  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.88/1.66  
% 3.88/1.66  %Foreground sorts:
% 3.88/1.66  
% 3.88/1.66  
% 3.88/1.66  %Background operators:
% 3.88/1.66  
% 3.88/1.66  
% 3.88/1.66  %Foreground operators:
% 3.88/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.88/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.66  
% 4.02/1.68  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.02/1.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.02/1.68  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.02/1.68  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.02/1.68  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.02/1.68  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.02/1.68  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.02/1.68  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.02/1.68  tff(f_45, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 4.02/1.68  tff(f_57, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 4.02/1.68  tff(c_2084, plain, (![A_99, B_100]: (r1_xboole_0(A_99, B_100) | k4_xboole_0(A_99, B_100)!=A_99)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.02/1.68  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.02/1.68  tff(c_2096, plain, (![B_101, A_102]: (r1_xboole_0(B_101, A_102) | k4_xboole_0(A_102, B_101)!=A_102)), inference(resolution, [status(thm)], [c_2084, c_2])).
% 4.02/1.68  tff(c_168, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.02/1.68  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.02/1.68  tff(c_29, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 4.02/1.68  tff(c_176, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_168, c_29])).
% 4.02/1.68  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.02/1.68  tff(c_47, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.02/1.68  tff(c_63, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(resolution, [status(thm)], [c_12, c_47])).
% 4.02/1.68  tff(c_193, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.02/1.68  tff(c_242, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_63, c_193])).
% 4.02/1.68  tff(c_26, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.02/1.68  tff(c_64, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.02/1.68  tff(c_68, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_64])).
% 4.02/1.68  tff(c_232, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_193])).
% 4.02/1.68  tff(c_245, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_232])).
% 4.02/1.68  tff(c_388, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.02/1.68  tff(c_422, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_245, c_388])).
% 4.02/1.68  tff(c_433, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_68, c_422])).
% 4.02/1.68  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.68  tff(c_16, plain, (![A_12, B_13, C_14]: (r1_xboole_0(A_12, k4_xboole_0(B_13, C_14)) | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.68  tff(c_514, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, k4_xboole_0(B_56, C_57)) | ~r1_xboole_0(A_55, C_57) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.02/1.68  tff(c_547, plain, (![A_55]: (~r1_xboole_0(A_55, k1_xboole_0) | ~r1_xboole_0(A_55, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_55, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_514])).
% 4.02/1.68  tff(c_714, plain, (![A_64]: (~r1_xboole_0(A_64, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_64, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_547])).
% 4.02/1.68  tff(c_949, plain, (![A_67]: (r1_xboole_0(A_67, '#skF_1') | ~r1_xboole_0(A_67, '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_714])).
% 4.02/1.68  tff(c_983, plain, (![A_68]: (r1_xboole_0(k4_xboole_0(A_68, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_949])).
% 4.02/1.68  tff(c_1013, plain, (![A_69]: (r1_xboole_0('#skF_1', k4_xboole_0(A_69, '#skF_2')))), inference(resolution, [status(thm)], [c_983, c_2])).
% 4.02/1.68  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.02/1.68  tff(c_1820, plain, (![A_83]: (k4_xboole_0('#skF_1', k4_xboole_0(A_83, '#skF_2'))='#skF_1')), inference(resolution, [status(thm)], [c_1013, c_18])).
% 4.02/1.68  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.02/1.68  tff(c_1853, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1820, c_10])).
% 4.02/1.68  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.02/1.68  tff(c_1910, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1853, c_8])).
% 4.02/1.68  tff(c_1916, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_433, c_242, c_1910])).
% 4.02/1.68  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_1916])).
% 4.02/1.68  tff(c_1919, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 4.02/1.68  tff(c_2107, plain, (k4_xboole_0('#skF_3', '#skF_1')!='#skF_3'), inference(resolution, [status(thm)], [c_2096, c_1919])).
% 4.02/1.68  tff(c_1921, plain, (![B_84, A_85]: (r1_xboole_0(B_84, A_85) | ~r1_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.02/1.68  tff(c_1926, plain, (![B_11, A_10]: (r1_xboole_0(B_11, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_14, c_1921])).
% 4.02/1.68  tff(c_1972, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.02/1.68  tff(c_1980, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_1972])).
% 4.02/1.68  tff(c_2543, plain, (![A_118, B_119, C_120]: (~r1_xboole_0(A_118, k4_xboole_0(B_119, C_120)) | ~r1_xboole_0(A_118, C_120) | r1_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.02/1.68  tff(c_2579, plain, (![A_118]: (~r1_xboole_0(A_118, k1_xboole_0) | ~r1_xboole_0(A_118, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_118, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_2543])).
% 4.02/1.68  tff(c_2672, plain, (![A_123]: (~r1_xboole_0(A_123, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_123, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2579])).
% 4.02/1.68  tff(c_2705, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1926, c_2672])).
% 4.02/1.68  tff(c_2711, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_2705, c_18])).
% 4.02/1.68  tff(c_2717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2107, c_2711])).
% 4.02/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.68  
% 4.02/1.68  Inference rules
% 4.02/1.68  ----------------------
% 4.02/1.68  #Ref     : 0
% 4.02/1.68  #Sup     : 684
% 4.02/1.68  #Fact    : 0
% 4.02/1.68  #Define  : 0
% 4.02/1.68  #Split   : 3
% 4.02/1.68  #Chain   : 0
% 4.02/1.68  #Close   : 0
% 4.02/1.68  
% 4.02/1.68  Ordering : KBO
% 4.02/1.68  
% 4.02/1.68  Simplification rules
% 4.02/1.68  ----------------------
% 4.02/1.68  #Subsume      : 40
% 4.02/1.68  #Demod        : 380
% 4.02/1.68  #Tautology    : 417
% 4.02/1.68  #SimpNegUnit  : 4
% 4.02/1.68  #BackRed      : 3
% 4.02/1.68  
% 4.02/1.68  #Partial instantiations: 0
% 4.02/1.68  #Strategies tried      : 1
% 4.02/1.68  
% 4.02/1.68  Timing (in seconds)
% 4.02/1.68  ----------------------
% 4.02/1.68  Preprocessing        : 0.28
% 4.02/1.68  Parsing              : 0.15
% 4.02/1.68  CNF conversion       : 0.02
% 4.02/1.68  Main loop            : 0.63
% 4.02/1.68  Inferencing          : 0.23
% 4.02/1.68  Reduction            : 0.22
% 4.02/1.68  Demodulation         : 0.17
% 4.02/1.68  BG Simplification    : 0.02
% 4.02/1.68  Subsumption          : 0.10
% 4.02/1.68  Abstraction          : 0.03
% 4.02/1.68  MUC search           : 0.00
% 4.02/1.68  Cooper               : 0.00
% 4.02/1.68  Total                : 0.94
% 4.02/1.68  Index Insertion      : 0.00
% 4.02/1.68  Index Deletion       : 0.00
% 4.02/1.68  Index Matching       : 0.00
% 4.02/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
