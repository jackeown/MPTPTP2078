%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 170 expanded)
%              Number of leaves         :   34 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 240 expanded)
%              Number of equality atoms :   40 ( 118 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_74,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_84,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_52,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_32,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_21] : k1_subset_1(A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = k2_subset_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_44])).

tff(c_60,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_xboole_0) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59])).

tff(c_46,plain,(
    ! [A_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_351,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_355,plain,(
    ! [A_28] : k3_subset_1(A_28,k3_subset_1(A_28,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_351])).

tff(c_358,plain,(
    ! [A_28] : k3_subset_1(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_355])).

tff(c_50,plain,
    ( k2_subset_1('#skF_5') != '#skF_6'
    | ~ r1_tarski(k3_subset_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,
    ( '#skF_5' != '#skF_6'
    | ~ r1_tarski(k3_subset_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_95,plain,(
    ~ r1_tarski(k3_subset_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r1_tarski(k3_subset_1('#skF_5','#skF_6'),'#skF_6')
    | k2_subset_1('#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,
    ( r1_tarski(k3_subset_1('#skF_5','#skF_6'),'#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_103,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_57])).

tff(c_104,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_95])).

tff(c_359,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_359])).

tff(c_363,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_666,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k3_subset_1(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_675,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_666])).

tff(c_34,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_550,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,B_100)
      | ~ r2_hidden(C_101,A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_559,plain,(
    ! [C_101,B_20,A_19] :
      ( ~ r2_hidden(C_101,B_20)
      | ~ r2_hidden(C_101,k4_xboole_0(A_19,B_20)) ) ),
    inference(resolution,[status(thm)],[c_34,c_550])).

tff(c_822,plain,(
    ! [C_121] :
      ( ~ r2_hidden(C_121,'#skF_6')
      | ~ r2_hidden(C_121,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_559])).

tff(c_837,plain,
    ( ~ r2_hidden('#skF_4'(k3_subset_1('#skF_5','#skF_6')),'#skF_6')
    | k3_subset_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_822])).

tff(c_858,plain,(
    ~ r2_hidden('#skF_4'(k3_subset_1('#skF_5','#skF_6')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_372,plain,(
    r1_tarski(k3_subset_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_57])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_376,plain,(
    k3_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_372,c_30])).

tff(c_378,plain,(
    ! [D_76,B_77,A_78] :
      ( r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k3_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_901,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_127,B_128)),B_128)
      | k3_xboole_0(A_127,B_128) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_378])).

tff(c_928,plain,
    ( r2_hidden('#skF_4'(k3_subset_1('#skF_5','#skF_6')),'#skF_6')
    | k3_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_901])).

tff(c_938,plain,
    ( r2_hidden('#skF_4'(k3_subset_1('#skF_5','#skF_6')),'#skF_6')
    | k3_subset_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_928])).

tff(c_939,plain,(
    k3_subset_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_858,c_938])).

tff(c_782,plain,(
    ! [A_118,B_119] :
      ( k3_subset_1(A_118,k3_subset_1(A_118,B_119)) = B_119
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_789,plain,(
    k3_subset_1('#skF_5',k3_subset_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_782])).

tff(c_944,plain,(
    k3_subset_1('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_789])).

tff(c_1000,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_60])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_1000])).

tff(c_1008,plain,(
    k3_subset_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_1012,plain,(
    k3_subset_1('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_789])).

tff(c_1029,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_60])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_1029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.47  
% 2.66/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.99/1.47  
% 2.99/1.47  %Foreground sorts:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Background operators:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Foreground operators:
% 2.99/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.99/1.47  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.99/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.99/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.47  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.99/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.99/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.47  
% 2.99/1.49  tff(f_68, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.99/1.49  tff(f_72, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.99/1.49  tff(f_74, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.99/1.49  tff(f_84, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.99/1.49  tff(f_86, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.99/1.49  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.99/1.49  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.99/1.49  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.99/1.49  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.99/1.49  tff(f_70, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.99/1.49  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.99/1.49  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.49  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.99/1.49  tff(c_32, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.49  tff(c_36, plain, (![A_21]: (k1_subset_1(A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.99/1.49  tff(c_38, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.99/1.49  tff(c_44, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=k2_subset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.49  tff(c_59, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_44])).
% 2.99/1.49  tff(c_60, plain, (![A_27]: (k3_subset_1(A_27, k1_xboole_0)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_59])).
% 2.99/1.49  tff(c_46, plain, (![A_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.99/1.49  tff(c_351, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.49  tff(c_355, plain, (![A_28]: (k3_subset_1(A_28, k3_subset_1(A_28, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_351])).
% 2.99/1.49  tff(c_358, plain, (![A_28]: (k3_subset_1(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_355])).
% 2.99/1.49  tff(c_50, plain, (k2_subset_1('#skF_5')!='#skF_6' | ~r1_tarski(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.99/1.49  tff(c_58, plain, ('#skF_5'!='#skF_6' | ~r1_tarski(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 2.99/1.49  tff(c_95, plain, (~r1_tarski(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.99/1.49  tff(c_56, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_6'), '#skF_6') | k2_subset_1('#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.99/1.49  tff(c_57, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_6'), '#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56])).
% 2.99/1.49  tff(c_103, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_95, c_57])).
% 2.99/1.49  tff(c_104, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_95])).
% 2.99/1.49  tff(c_359, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_104])).
% 2.99/1.49  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_359])).
% 2.99/1.49  tff(c_363, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 2.99/1.49  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.99/1.49  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.99/1.49  tff(c_666, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k3_subset_1(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.99/1.49  tff(c_675, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_666])).
% 2.99/1.49  tff(c_34, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_550, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, B_100) | ~r2_hidden(C_101, A_99))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.49  tff(c_559, plain, (![C_101, B_20, A_19]: (~r2_hidden(C_101, B_20) | ~r2_hidden(C_101, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_34, c_550])).
% 2.99/1.49  tff(c_822, plain, (![C_121]: (~r2_hidden(C_121, '#skF_6') | ~r2_hidden(C_121, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_675, c_559])).
% 2.99/1.49  tff(c_837, plain, (~r2_hidden('#skF_4'(k3_subset_1('#skF_5', '#skF_6')), '#skF_6') | k3_subset_1('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_822])).
% 2.99/1.49  tff(c_858, plain, (~r2_hidden('#skF_4'(k3_subset_1('#skF_5', '#skF_6')), '#skF_6')), inference(splitLeft, [status(thm)], [c_837])).
% 2.99/1.49  tff(c_372, plain, (r1_tarski(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_363, c_57])).
% 2.99/1.49  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.99/1.49  tff(c_376, plain, (k3_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_372, c_30])).
% 2.99/1.49  tff(c_378, plain, (![D_76, B_77, A_78]: (r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k3_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.49  tff(c_901, plain, (![A_127, B_128]: (r2_hidden('#skF_4'(k3_xboole_0(A_127, B_128)), B_128) | k3_xboole_0(A_127, B_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_378])).
% 2.99/1.49  tff(c_928, plain, (r2_hidden('#skF_4'(k3_subset_1('#skF_5', '#skF_6')), '#skF_6') | k3_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_376, c_901])).
% 2.99/1.49  tff(c_938, plain, (r2_hidden('#skF_4'(k3_subset_1('#skF_5', '#skF_6')), '#skF_6') | k3_subset_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_376, c_928])).
% 2.99/1.49  tff(c_939, plain, (k3_subset_1('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_858, c_938])).
% 2.99/1.49  tff(c_782, plain, (![A_118, B_119]: (k3_subset_1(A_118, k3_subset_1(A_118, B_119))=B_119 | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.49  tff(c_789, plain, (k3_subset_1('#skF_5', k3_subset_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_48, c_782])).
% 2.99/1.49  tff(c_944, plain, (k3_subset_1('#skF_5', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_789])).
% 2.99/1.49  tff(c_1000, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_944, c_60])).
% 2.99/1.49  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_1000])).
% 2.99/1.49  tff(c_1008, plain, (k3_subset_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_837])).
% 2.99/1.49  tff(c_1012, plain, (k3_subset_1('#skF_5', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_789])).
% 2.99/1.49  tff(c_1029, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1012, c_60])).
% 2.99/1.49  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_1029])).
% 2.99/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.49  
% 2.99/1.49  Inference rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Ref     : 0
% 2.99/1.49  #Sup     : 235
% 2.99/1.49  #Fact    : 0
% 2.99/1.49  #Define  : 0
% 2.99/1.49  #Split   : 2
% 2.99/1.49  #Chain   : 0
% 2.99/1.49  #Close   : 0
% 2.99/1.49  
% 2.99/1.49  Ordering : KBO
% 2.99/1.49  
% 2.99/1.49  Simplification rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Subsume      : 61
% 2.99/1.49  #Demod        : 98
% 2.99/1.49  #Tautology    : 106
% 2.99/1.49  #SimpNegUnit  : 7
% 2.99/1.49  #BackRed      : 26
% 2.99/1.49  
% 2.99/1.49  #Partial instantiations: 0
% 2.99/1.49  #Strategies tried      : 1
% 2.99/1.49  
% 2.99/1.49  Timing (in seconds)
% 2.99/1.49  ----------------------
% 2.99/1.49  Preprocessing        : 0.33
% 2.99/1.49  Parsing              : 0.17
% 2.99/1.49  CNF conversion       : 0.03
% 2.99/1.49  Main loop            : 0.34
% 2.99/1.49  Inferencing          : 0.12
% 2.99/1.49  Reduction            : 0.11
% 2.99/1.49  Demodulation         : 0.08
% 2.99/1.49  BG Simplification    : 0.02
% 2.99/1.49  Subsumption          : 0.06
% 2.99/1.49  Abstraction          : 0.02
% 2.99/1.49  MUC search           : 0.00
% 2.99/1.49  Cooper               : 0.00
% 2.99/1.49  Total                : 0.70
% 2.99/1.49  Index Insertion      : 0.00
% 2.99/1.49  Index Deletion       : 0.00
% 2.99/1.49  Index Matching       : 0.00
% 2.99/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
