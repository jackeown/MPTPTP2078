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
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 101 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :   74 ( 126 expanded)
%              Number of equality atoms :   36 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_105,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_105])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_953,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_966,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_953])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1007,plain,(
    r1_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_20])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_163,plain,(
    ! [A_54,B_55] :
      ( ~ r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_171,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_163])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_440,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_478,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_440])).

tff(c_485,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_478])).

tff(c_492,plain,(
    ! [A_75] : k4_xboole_0(A_75,A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_478])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_497,plain,(
    ! [A_75] : k4_xboole_0(A_75,k1_xboole_0) = k3_xboole_0(A_75,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_16])).

tff(c_533,plain,(
    ! [A_76] : k3_xboole_0(A_76,A_76) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_497])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_539,plain,(
    ! [A_76] : k5_xboole_0(A_76,A_76) = k4_xboole_0(A_76,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_10])).

tff(c_563,plain,(
    ! [A_76] : k5_xboole_0(A_76,A_76) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_539])).

tff(c_52,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_113,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_105])).

tff(c_285,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_303,plain,(
    k5_xboole_0('#skF_6','#skF_6') = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_285])).

tff(c_573,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_303])).

tff(c_1024,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,k4_xboole_0(B_95,C_96))
      | ~ r1_xboole_0(A_94,C_96)
      | r1_xboole_0(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1045,plain,(
    ! [A_94] :
      ( ~ r1_xboole_0(A_94,k1_xboole_0)
      | ~ r1_xboole_0(A_94,'#skF_7')
      | r1_xboole_0(A_94,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_1024])).

tff(c_1224,plain,(
    ! [A_99] :
      ( ~ r1_xboole_0(A_99,'#skF_7')
      | r1_xboole_0(A_99,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1045])).

tff(c_1236,plain,(
    r1_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1007,c_1224])).

tff(c_160,plain,(
    ! [A_51,B_52] :
      ( ~ r1_xboole_0(A_51,B_52)
      | k3_xboole_0(A_51,B_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_1243,plain,(
    k3_xboole_0(k3_subset_1('#skF_5','#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1236,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1408,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_2])).

tff(c_1426,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1408])).

tff(c_1428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1426])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.61  
% 3.32/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 3.32/1.62  
% 3.32/1.62  %Foreground sorts:
% 3.32/1.62  
% 3.32/1.62  
% 3.32/1.62  %Background operators:
% 3.32/1.62  
% 3.32/1.62  
% 3.32/1.62  %Foreground operators:
% 3.32/1.62  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.32/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.32/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.62  
% 3.32/1.63  tff(f_107, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.32/1.63  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.32/1.63  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.32/1.63  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.32/1.63  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.32/1.63  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.32/1.63  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.32/1.63  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.32/1.63  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.32/1.63  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.32/1.63  tff(f_71, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 3.32/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.32/1.63  tff(c_48, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.32/1.63  tff(c_50, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.32/1.63  tff(c_105, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.63  tff(c_112, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_50, c_105])).
% 3.32/1.63  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.32/1.63  tff(c_953, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.32/1.63  tff(c_966, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_953])).
% 3.32/1.63  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.63  tff(c_1007, plain, (r1_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_966, c_20])).
% 3.32/1.63  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.63  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.63  tff(c_143, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.63  tff(c_163, plain, (![A_54, B_55]: (~r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_143])).
% 3.32/1.63  tff(c_171, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_163])).
% 3.32/1.63  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.32/1.63  tff(c_440, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.63  tff(c_478, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_440])).
% 3.32/1.63  tff(c_485, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_478])).
% 3.32/1.63  tff(c_492, plain, (![A_75]: (k4_xboole_0(A_75, A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_478])).
% 3.32/1.63  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.63  tff(c_497, plain, (![A_75]: (k4_xboole_0(A_75, k1_xboole_0)=k3_xboole_0(A_75, A_75))), inference(superposition, [status(thm), theory('equality')], [c_492, c_16])).
% 3.32/1.63  tff(c_533, plain, (![A_76]: (k3_xboole_0(A_76, A_76)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_497])).
% 3.32/1.63  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.63  tff(c_539, plain, (![A_76]: (k5_xboole_0(A_76, A_76)=k4_xboole_0(A_76, A_76))), inference(superposition, [status(thm), theory('equality')], [c_533, c_10])).
% 3.32/1.63  tff(c_563, plain, (![A_76]: (k5_xboole_0(A_76, A_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_485, c_539])).
% 3.32/1.63  tff(c_52, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.32/1.63  tff(c_113, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_52, c_105])).
% 3.32/1.63  tff(c_285, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.63  tff(c_303, plain, (k5_xboole_0('#skF_6', '#skF_6')=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_113, c_285])).
% 3.32/1.63  tff(c_573, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_563, c_303])).
% 3.32/1.63  tff(c_1024, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, k4_xboole_0(B_95, C_96)) | ~r1_xboole_0(A_94, C_96) | r1_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.32/1.63  tff(c_1045, plain, (![A_94]: (~r1_xboole_0(A_94, k1_xboole_0) | ~r1_xboole_0(A_94, '#skF_7') | r1_xboole_0(A_94, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_1024])).
% 3.32/1.63  tff(c_1224, plain, (![A_99]: (~r1_xboole_0(A_99, '#skF_7') | r1_xboole_0(A_99, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1045])).
% 3.32/1.63  tff(c_1236, plain, (r1_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_1007, c_1224])).
% 3.32/1.63  tff(c_160, plain, (![A_51, B_52]: (~r1_xboole_0(A_51, B_52) | k3_xboole_0(A_51, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_143])).
% 3.32/1.63  tff(c_1243, plain, (k3_xboole_0(k3_subset_1('#skF_5', '#skF_7'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1236, c_160])).
% 3.32/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.63  tff(c_1408, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1243, c_2])).
% 3.32/1.63  tff(c_1426, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1408])).
% 3.32/1.63  tff(c_1428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1426])).
% 3.32/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.63  
% 3.32/1.63  Inference rules
% 3.32/1.63  ----------------------
% 3.32/1.63  #Ref     : 0
% 3.32/1.63  #Sup     : 341
% 3.32/1.63  #Fact    : 0
% 3.32/1.63  #Define  : 0
% 3.32/1.63  #Split   : 6
% 3.32/1.63  #Chain   : 0
% 3.32/1.63  #Close   : 0
% 3.32/1.63  
% 3.32/1.63  Ordering : KBO
% 3.32/1.63  
% 3.32/1.63  Simplification rules
% 3.32/1.63  ----------------------
% 3.32/1.63  #Subsume      : 15
% 3.32/1.63  #Demod        : 168
% 3.32/1.63  #Tautology    : 211
% 3.32/1.63  #SimpNegUnit  : 13
% 3.32/1.63  #BackRed      : 3
% 3.32/1.63  
% 3.32/1.63  #Partial instantiations: 0
% 3.32/1.63  #Strategies tried      : 1
% 3.32/1.63  
% 3.32/1.63  Timing (in seconds)
% 3.32/1.63  ----------------------
% 3.32/1.63  Preprocessing        : 0.35
% 3.32/1.63  Parsing              : 0.18
% 3.32/1.63  CNF conversion       : 0.03
% 3.32/1.63  Main loop            : 0.44
% 3.32/1.63  Inferencing          : 0.15
% 3.32/1.63  Reduction            : 0.16
% 3.32/1.63  Demodulation         : 0.12
% 3.32/1.63  BG Simplification    : 0.02
% 3.32/1.63  Subsumption          : 0.07
% 3.32/1.63  Abstraction          : 0.02
% 3.32/1.63  MUC search           : 0.00
% 3.32/1.63  Cooper               : 0.00
% 3.32/1.63  Total                : 0.82
% 3.32/1.63  Index Insertion      : 0.00
% 3.32/1.63  Index Deletion       : 0.00
% 3.32/1.63  Index Matching       : 0.00
% 3.32/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
