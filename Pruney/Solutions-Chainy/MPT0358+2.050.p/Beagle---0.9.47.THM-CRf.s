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
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 150 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 208 expanded)
%              Number of equality atoms :   34 ( 106 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_73,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_79,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_64,plain,(
    ! [A_33] : k1_subset_1(A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,
    ( k1_subset_1('#skF_7') != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_80,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_78,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_subset_1('#skF_7') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_79,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_78])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_79])).

tff(c_36,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,(
    ! [A_20] : k3_xboole_0(A_20,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_36])).

tff(c_42,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_119,plain,(
    ! [A_25] : k5_xboole_0(A_25,'#skF_8') = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_42])).

tff(c_240,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_252,plain,(
    ! [A_20] : k5_xboole_0(A_20,'#skF_8') = k4_xboole_0(A_20,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_240])).

tff(c_256,plain,(
    ! [A_20] : k4_xboole_0(A_20,'#skF_8') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_252])).

tff(c_329,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_353,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_329])).

tff(c_359,plain,(
    ! [A_83] : k4_xboole_0(A_83,A_83) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_353])).

tff(c_38,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_374,plain,(
    ! [A_83] : r1_tarski('#skF_8',A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_38])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_114])).

tff(c_390,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_392,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_79])).

tff(c_405,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_412,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_392,c_405])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_849,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,B_132) = k3_subset_1(A_131,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_862,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_849])).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_564,plain,(
    ! [D_113,B_114,A_115] :
      ( ~ r2_hidden(D_113,B_114)
      | ~ r2_hidden(D_113,k4_xboole_0(A_115,B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4710,plain,(
    ! [A_272,A_273,B_274] :
      ( ~ r2_hidden('#skF_3'(A_272,k4_xboole_0(A_273,B_274)),B_274)
      | r1_xboole_0(A_272,k4_xboole_0(A_273,B_274)) ) ),
    inference(resolution,[status(thm)],[c_26,c_564])).

tff(c_4813,plain,(
    ! [A_275,A_276] : r1_xboole_0(A_275,k4_xboole_0(A_276,A_275)) ),
    inference(resolution,[status(thm)],[c_28,c_4710])).

tff(c_4845,plain,(
    r1_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_4813])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4876,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4845,c_20])).

tff(c_4879,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_4876])).

tff(c_4881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_4879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.10  
% 5.60/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_5
% 5.60/2.10  
% 5.60/2.10  %Foreground sorts:
% 5.60/2.10  
% 5.60/2.10  
% 5.60/2.10  %Background operators:
% 5.60/2.10  
% 5.60/2.10  
% 5.60/2.10  %Foreground operators:
% 5.60/2.10  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.60/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.60/2.10  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.60/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.60/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.60/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.10  tff('#skF_7', type, '#skF_7': $i).
% 5.60/2.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.60/2.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.60/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.10  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.60/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.60/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.60/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.10  tff('#skF_8', type, '#skF_8': $i).
% 5.60/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.10  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.60/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.60/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.60/2.10  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.60/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.10  
% 5.71/2.12  tff(f_101, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 5.71/2.12  tff(f_115, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 5.71/2.12  tff(f_73, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.71/2.12  tff(f_79, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.71/2.12  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.71/2.12  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.71/2.12  tff(f_75, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.71/2.12  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.71/2.12  tff(f_105, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.71/2.12  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.71/2.12  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.71/2.12  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.71/2.12  tff(c_64, plain, (![A_33]: (k1_subset_1(A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.71/2.12  tff(c_72, plain, (k1_subset_1('#skF_7')!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.71/2.12  tff(c_80, plain, (k1_xboole_0!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72])).
% 5.71/2.12  tff(c_114, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_80])).
% 5.71/2.12  tff(c_78, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_subset_1('#skF_7')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.71/2.12  tff(c_79, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_78])).
% 5.71/2.12  tff(c_115, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_114, c_79])).
% 5.71/2.12  tff(c_36, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.71/2.12  tff(c_118, plain, (![A_20]: (k3_xboole_0(A_20, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_36])).
% 5.71/2.12  tff(c_42, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.71/2.12  tff(c_119, plain, (![A_25]: (k5_xboole_0(A_25, '#skF_8')=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_42])).
% 5.71/2.12  tff(c_240, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.71/2.12  tff(c_252, plain, (![A_20]: (k5_xboole_0(A_20, '#skF_8')=k4_xboole_0(A_20, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_240])).
% 5.71/2.12  tff(c_256, plain, (![A_20]: (k4_xboole_0(A_20, '#skF_8')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_252])).
% 5.71/2.12  tff(c_329, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.71/2.12  tff(c_353, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_256, c_329])).
% 5.71/2.12  tff(c_359, plain, (![A_83]: (k4_xboole_0(A_83, A_83)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_353])).
% 5.71/2.12  tff(c_38, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.71/2.12  tff(c_374, plain, (![A_83]: (r1_tarski('#skF_8', A_83))), inference(superposition, [status(thm), theory('equality')], [c_359, c_38])).
% 5.71/2.12  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_114])).
% 5.71/2.12  tff(c_390, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 5.71/2.12  tff(c_392, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_390, c_79])).
% 5.71/2.12  tff(c_405, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.71/2.12  tff(c_412, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_392, c_405])).
% 5.71/2.12  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.71/2.12  tff(c_849, plain, (![A_131, B_132]: (k4_xboole_0(A_131, B_132)=k3_subset_1(A_131, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.71/2.12  tff(c_862, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_849])).
% 5.71/2.12  tff(c_28, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.12  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.12  tff(c_564, plain, (![D_113, B_114, A_115]: (~r2_hidden(D_113, B_114) | ~r2_hidden(D_113, k4_xboole_0(A_115, B_114)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.71/2.12  tff(c_4710, plain, (![A_272, A_273, B_274]: (~r2_hidden('#skF_3'(A_272, k4_xboole_0(A_273, B_274)), B_274) | r1_xboole_0(A_272, k4_xboole_0(A_273, B_274)))), inference(resolution, [status(thm)], [c_26, c_564])).
% 5.71/2.12  tff(c_4813, plain, (![A_275, A_276]: (r1_xboole_0(A_275, k4_xboole_0(A_276, A_275)))), inference(resolution, [status(thm)], [c_28, c_4710])).
% 5.71/2.12  tff(c_4845, plain, (r1_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_862, c_4813])).
% 5.71/2.12  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.71/2.12  tff(c_4876, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4845, c_20])).
% 5.71/2.12  tff(c_4879, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_4876])).
% 5.71/2.12  tff(c_4881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_4879])).
% 5.71/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.12  
% 5.71/2.12  Inference rules
% 5.71/2.12  ----------------------
% 5.71/2.12  #Ref     : 0
% 5.71/2.12  #Sup     : 1130
% 5.71/2.12  #Fact    : 0
% 5.71/2.12  #Define  : 0
% 5.71/2.12  #Split   : 9
% 5.71/2.12  #Chain   : 0
% 5.71/2.12  #Close   : 0
% 5.71/2.12  
% 5.71/2.12  Ordering : KBO
% 5.71/2.12  
% 5.71/2.12  Simplification rules
% 5.71/2.12  ----------------------
% 5.71/2.12  #Subsume      : 112
% 5.71/2.12  #Demod        : 682
% 5.71/2.12  #Tautology    : 531
% 5.71/2.12  #SimpNegUnit  : 46
% 5.71/2.12  #BackRed      : 21
% 5.71/2.12  
% 5.71/2.12  #Partial instantiations: 0
% 5.71/2.12  #Strategies tried      : 1
% 5.71/2.12  
% 5.71/2.12  Timing (in seconds)
% 5.71/2.12  ----------------------
% 5.71/2.12  Preprocessing        : 0.33
% 5.71/2.12  Parsing              : 0.17
% 5.71/2.12  CNF conversion       : 0.03
% 5.71/2.12  Main loop            : 1.02
% 5.71/2.12  Inferencing          : 0.34
% 5.71/2.12  Reduction            : 0.36
% 5.71/2.12  Demodulation         : 0.26
% 5.71/2.12  BG Simplification    : 0.04
% 5.71/2.12  Subsumption          : 0.19
% 5.71/2.12  Abstraction          : 0.05
% 5.71/2.12  MUC search           : 0.00
% 5.71/2.12  Cooper               : 0.00
% 5.71/2.12  Total                : 1.38
% 5.71/2.12  Index Insertion      : 0.00
% 5.71/2.12  Index Deletion       : 0.00
% 5.71/2.12  Index Matching       : 0.00
% 5.71/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
