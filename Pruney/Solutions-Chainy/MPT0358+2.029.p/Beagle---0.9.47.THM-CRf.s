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
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 170 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 247 expanded)
%              Number of equality atoms :   30 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

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

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_14,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_95,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_95])).

tff(c_167,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_182,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_167])).

tff(c_191,plain,(
    ! [A_35] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_167])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    ! [A_36] : r1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_16])).

tff(c_204,plain,(
    ! [A_14,A_36] : r1_xboole_0(k4_xboole_0(k1_xboole_0,A_14),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_203])).

tff(c_18,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_76,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_30,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_32])).

tff(c_84,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_76])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_102,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_94,c_95])).

tff(c_209,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_212,plain,(
    ! [C_41] :
      ( ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))
      | ~ r2_hidden(C_41,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_209])).

tff(c_255,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_473,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_477,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_473])).

tff(c_218,plain,(
    ! [A_14,C_41] :
      ( ~ r1_xboole_0(k1_xboole_0,A_14)
      | ~ r2_hidden(C_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_209])).

tff(c_230,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_327,plain,(
    ! [A_50,B_51] :
      ( ~ r1_xboole_0(A_50,B_51)
      | k3_xboole_0(A_50,B_51) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_209])).

tff(c_346,plain,(
    ! [A_52,B_53] : k3_xboole_0(k4_xboole_0(A_52,B_53),B_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_327])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_401,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,k4_xboole_0(A_55,B_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_406,plain,(
    ! [B_54,A_55] :
      ( r2_hidden('#skF_1'(B_54,k4_xboole_0(A_55,B_54)),k1_xboole_0)
      | r1_xboole_0(B_54,k4_xboole_0(A_55,B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_4])).

tff(c_434,plain,(
    ! [B_54,A_55] : r1_xboole_0(B_54,k4_xboole_0(A_55,B_54)) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_406])).

tff(c_483,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_434])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_483])).

tff(c_506,plain,(
    ! [C_62] : ~ r2_hidden(C_62,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_510,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_506])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_510])).

tff(c_515,plain,(
    ! [A_14] : ~ r1_xboole_0(k1_xboole_0,A_14) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_104,plain,(
    ! [A_31] : k3_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_95])).

tff(c_109,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2])).

tff(c_215,plain,(
    ! [A_31,C_41] :
      ( ~ r1_xboole_0(A_31,k1_xboole_0)
      | ~ r2_hidden(C_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_209])).

tff(c_534,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_666,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),k3_xboole_0(A_74,B_75))
      | r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_681,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(k1_xboole_0,A_14),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_666])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_534,c_681])).

tff(c_695,plain,(
    ! [A_76] : ~ r1_xboole_0(A_76,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_703,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_204,c_695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.58  
% 2.65/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.65/1.58  
% 2.65/1.58  %Foreground sorts:
% 2.65/1.58  
% 2.65/1.58  
% 2.65/1.58  %Background operators:
% 2.65/1.58  
% 2.65/1.58  
% 2.65/1.58  %Foreground operators:
% 2.65/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.65/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.65/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.58  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.65/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.58  
% 2.65/1.60  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.60  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/1.60  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.65/1.60  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.65/1.60  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.65/1.60  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.65/1.60  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.65/1.60  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.65/1.60  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.65/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.60  tff(c_14, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.60  tff(c_95, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.60  tff(c_103, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_95])).
% 2.65/1.60  tff(c_167, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.60  tff(c_182, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_103, c_167])).
% 2.65/1.60  tff(c_191, plain, (![A_35]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_35))), inference(superposition, [status(thm), theory('equality')], [c_103, c_167])).
% 2.65/1.60  tff(c_16, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.60  tff(c_203, plain, (![A_36]: (r1_xboole_0(k5_xboole_0(k1_xboole_0, k1_xboole_0), A_36))), inference(superposition, [status(thm), theory('equality')], [c_191, c_16])).
% 2.65/1.60  tff(c_204, plain, (![A_14, A_36]: (r1_xboole_0(k4_xboole_0(k1_xboole_0, A_14), A_36))), inference(superposition, [status(thm), theory('equality')], [c_182, c_203])).
% 2.65/1.60  tff(c_18, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.60  tff(c_24, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.60  tff(c_31, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 2.65/1.60  tff(c_76, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_31])).
% 2.65/1.60  tff(c_30, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.60  tff(c_32, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30])).
% 2.65/1.60  tff(c_82, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_76, c_32])).
% 2.65/1.60  tff(c_84, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_14])).
% 2.65/1.60  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_76])).
% 2.65/1.60  tff(c_93, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_31])).
% 2.65/1.60  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.60  tff(c_94, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_31])).
% 2.65/1.60  tff(c_102, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_94, c_95])).
% 2.65/1.60  tff(c_209, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.60  tff(c_212, plain, (![C_41]: (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | ~r2_hidden(C_41, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_209])).
% 2.65/1.60  tff(c_255, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_212])).
% 2.65/1.60  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.60  tff(c_473, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.60  tff(c_477, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_473])).
% 2.65/1.60  tff(c_218, plain, (![A_14, C_41]: (~r1_xboole_0(k1_xboole_0, A_14) | ~r2_hidden(C_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_209])).
% 2.65/1.60  tff(c_230, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_218])).
% 2.65/1.60  tff(c_327, plain, (![A_50, B_51]: (~r1_xboole_0(A_50, B_51) | k3_xboole_0(A_50, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_209])).
% 2.65/1.60  tff(c_346, plain, (![A_52, B_53]: (k3_xboole_0(k4_xboole_0(A_52, B_53), B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_327])).
% 2.65/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.60  tff(c_401, plain, (![B_54, A_55]: (k3_xboole_0(B_54, k4_xboole_0(A_55, B_54))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_346, c_2])).
% 2.65/1.60  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.60  tff(c_406, plain, (![B_54, A_55]: (r2_hidden('#skF_1'(B_54, k4_xboole_0(A_55, B_54)), k1_xboole_0) | r1_xboole_0(B_54, k4_xboole_0(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_401, c_4])).
% 2.65/1.60  tff(c_434, plain, (![B_54, A_55]: (r1_xboole_0(B_54, k4_xboole_0(A_55, B_54)))), inference(negUnitSimplification, [status(thm)], [c_230, c_406])).
% 2.65/1.60  tff(c_483, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_434])).
% 2.65/1.60  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_483])).
% 2.65/1.60  tff(c_506, plain, (![C_62]: (~r2_hidden(C_62, '#skF_4'))), inference(splitRight, [status(thm)], [c_212])).
% 2.65/1.60  tff(c_510, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_506])).
% 2.65/1.60  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_510])).
% 2.65/1.60  tff(c_515, plain, (![A_14]: (~r1_xboole_0(k1_xboole_0, A_14))), inference(splitRight, [status(thm)], [c_218])).
% 2.65/1.60  tff(c_104, plain, (![A_31]: (k3_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_95])).
% 2.65/1.60  tff(c_109, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_2])).
% 2.65/1.60  tff(c_215, plain, (![A_31, C_41]: (~r1_xboole_0(A_31, k1_xboole_0) | ~r2_hidden(C_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_109, c_209])).
% 2.65/1.60  tff(c_534, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_215])).
% 2.65/1.60  tff(c_666, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), k3_xboole_0(A_74, B_75)) | r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.60  tff(c_681, plain, (![A_14]: (r2_hidden('#skF_1'(k1_xboole_0, A_14), k1_xboole_0) | r1_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_103, c_666])).
% 2.65/1.60  tff(c_693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_534, c_681])).
% 2.65/1.60  tff(c_695, plain, (![A_76]: (~r1_xboole_0(A_76, k1_xboole_0))), inference(splitRight, [status(thm)], [c_215])).
% 2.65/1.60  tff(c_703, plain, $false, inference(resolution, [status(thm)], [c_204, c_695])).
% 2.65/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.60  
% 2.65/1.60  Inference rules
% 2.65/1.60  ----------------------
% 2.65/1.60  #Ref     : 0
% 2.65/1.60  #Sup     : 186
% 2.65/1.60  #Fact    : 0
% 2.65/1.60  #Define  : 0
% 2.65/1.60  #Split   : 4
% 2.65/1.60  #Chain   : 0
% 2.65/1.60  #Close   : 0
% 2.65/1.60  
% 2.65/1.60  Ordering : KBO
% 2.65/1.60  
% 2.65/1.60  Simplification rules
% 2.65/1.60  ----------------------
% 2.65/1.60  #Subsume      : 34
% 2.65/1.60  #Demod        : 45
% 2.65/1.60  #Tautology    : 84
% 2.65/1.60  #SimpNegUnit  : 12
% 2.65/1.60  #BackRed      : 6
% 2.65/1.60  
% 2.65/1.60  #Partial instantiations: 0
% 2.65/1.60  #Strategies tried      : 1
% 2.65/1.60  
% 2.65/1.60  Timing (in seconds)
% 2.65/1.60  ----------------------
% 2.65/1.60  Preprocessing        : 0.43
% 2.65/1.60  Parsing              : 0.20
% 2.65/1.60  CNF conversion       : 0.03
% 2.65/1.60  Main loop            : 0.33
% 2.65/1.60  Inferencing          : 0.12
% 2.65/1.60  Reduction            : 0.12
% 2.65/1.60  Demodulation         : 0.09
% 2.65/1.60  BG Simplification    : 0.02
% 2.65/1.60  Subsumption          : 0.05
% 2.65/1.60  Abstraction          : 0.03
% 2.65/1.60  MUC search           : 0.00
% 2.65/1.60  Cooper               : 0.00
% 2.65/1.60  Total                : 0.80
% 2.65/1.60  Index Insertion      : 0.00
% 2.65/1.60  Index Deletion       : 0.00
% 2.65/1.60  Index Matching       : 0.00
% 2.65/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
