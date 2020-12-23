%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.35s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 244 expanded)
%              Number of leaves         :   36 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 265 expanded)
%              Number of equality atoms :   29 ( 186 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k4_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_467,plain,(
    ! [A_93,B_94] : k5_xboole_0(k5_xboole_0(A_93,B_94),k2_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_516,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,A_16)) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_467])).

tff(c_519,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_516])).

tff(c_520,plain,(
    ! [A_95] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_95,A_95)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_516])).

tff(c_192,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_222,plain,(
    ! [A_16,C_86] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_86)) = k5_xboole_0(k1_xboole_0,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_192])).

tff(c_532,plain,(
    ! [A_95] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_95,A_95)) = k5_xboole_0(k1_xboole_0,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_222])).

tff(c_543,plain,(
    ! [A_95] : k5_xboole_0(k1_xboole_0,A_95) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_532])).

tff(c_313,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_192])).

tff(c_373,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_313])).

tff(c_669,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_373])).

tff(c_206,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k5_xboole_0(B_85,k5_xboole_0(A_84,B_85))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_18])).

tff(c_722,plain,(
    ! [A_103,C_104] : k5_xboole_0(A_103,k5_xboole_0(A_103,C_104)) = C_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_222])).

tff(c_775,plain,(
    ! [B_85,A_84] : k5_xboole_0(B_85,k5_xboole_0(A_84,B_85)) = k5_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_722])).

tff(c_856,plain,(
    ! [B_108,A_109] : k5_xboole_0(B_108,k5_xboole_0(A_109,B_108)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_775])).

tff(c_922,plain,(
    ! [A_5,B_6] : k5_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_856])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_810,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_tarski(k5_xboole_0(A_105,C_106),B_107)
      | ~ r1_tarski(C_106,B_107)
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11026,plain,(
    ! [A_313,B_314,C_315,B_316] :
      ( r1_tarski(k5_xboole_0(A_313,k5_xboole_0(B_314,C_315)),B_316)
      | ~ r1_tarski(C_315,B_316)
      | ~ r1_tarski(k5_xboole_0(A_313,B_314),B_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_810])).

tff(c_11306,plain,(
    ! [A_313,B_316,A_16] :
      ( r1_tarski(k5_xboole_0(A_313,k1_xboole_0),B_316)
      | ~ r1_tarski(A_16,B_316)
      | ~ r1_tarski(k5_xboole_0(A_313,A_16),B_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_11026])).

tff(c_35937,plain,(
    ! [A_415,B_416,A_417] :
      ( r1_tarski(A_415,B_416)
      | ~ r1_tarski(A_417,B_416)
      | ~ r1_tarski(k5_xboole_0(A_415,A_417),B_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_11306])).

tff(c_36204,plain,(
    ! [A_418,A_419] :
      ( r1_tarski(A_418,k5_xboole_0(A_418,A_419))
      | ~ r1_tarski(A_419,k5_xboole_0(A_418,A_419)) ) ),
    inference(resolution,[status(thm)],[c_8,c_35937])).

tff(c_36344,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,B_6),k5_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)))
      | ~ r1_tarski(k4_xboole_0(A_5,B_6),A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_36204])).

tff(c_39121,plain,(
    ! [A_453,B_454] :
      ( r1_tarski(k3_xboole_0(A_453,B_454),A_453)
      | ~ r1_tarski(k4_xboole_0(A_453,B_454),A_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_36344])).

tff(c_39144,plain,(
    ! [B_8,C_9] :
      ( r1_tarski(k3_xboole_0(B_8,C_9),B_8)
      | ~ r1_tarski(B_8,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_39121])).

tff(c_39160,plain,(
    ! [B_8,C_9] : r1_tarski(k3_xboole_0(B_8,C_9),B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_39144])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_639,plain,(
    ! [A_98,B_99,C_100] :
      ( k9_subset_1(A_98,B_99,C_100) = k3_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_644,plain,(
    ! [B_99] : k9_subset_1('#skF_1',B_99,'#skF_3') = k3_xboole_0(B_99,'#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_639])).

tff(c_1443,plain,(
    ! [A_125,B_126,C_127] :
      ( m1_subset_1(k9_subset_1(A_125,B_126,C_127),k1_zfmisc_1(A_125))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1448,plain,(
    ! [B_99] :
      ( m1_subset_1(k3_xboole_0(B_99,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_1443])).

tff(c_1454,plain,(
    ! [B_99] : m1_subset_1(k3_xboole_0(B_99,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1448])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2395,plain,(
    ! [A_177,C_178,B_179] :
      ( r1_tarski(k3_subset_1(A_177,C_178),k3_subset_1(A_177,B_179))
      | ~ r1_tarski(B_179,C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(A_177))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1316,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_44])).

tff(c_2398,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2395,c_1316])).

tff(c_2403,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1454,c_48,c_2398])).

tff(c_39171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39160,c_2403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.31/8.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/8.77  
% 15.35/8.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/8.78  %$ r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.35/8.78  
% 15.35/8.78  %Foreground sorts:
% 15.35/8.78  
% 15.35/8.78  
% 15.35/8.78  %Background operators:
% 15.35/8.78  
% 15.35/8.78  
% 15.35/8.78  %Foreground operators:
% 15.35/8.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.35/8.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.35/8.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.35/8.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.35/8.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.35/8.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.35/8.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.35/8.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.35/8.78  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.35/8.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.35/8.78  tff('#skF_2', type, '#skF_2': $i).
% 15.35/8.78  tff('#skF_3', type, '#skF_3': $i).
% 15.35/8.78  tff('#skF_1', type, '#skF_1': $i).
% 15.35/8.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.35/8.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.35/8.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.35/8.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.35/8.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 15.35/8.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.35/8.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.35/8.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.35/8.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.35/8.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.35/8.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.35/8.78  
% 15.35/8.79  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.35/8.79  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 15.35/8.79  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.35/8.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 15.35/8.79  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 15.35/8.79  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 15.35/8.79  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 15.35/8.79  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 15.35/8.79  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 15.35/8.79  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.35/8.79  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 15.35/8.79  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 15.35/8.79  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.35/8.79  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(k4_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.35/8.79  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.35/8.79  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.35/8.79  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.35/8.79  tff(c_467, plain, (![A_93, B_94]: (k5_xboole_0(k5_xboole_0(A_93, B_94), k2_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.35/8.79  tff(c_516, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, A_16))=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_467])).
% 15.35/8.79  tff(c_519, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_516])).
% 15.35/8.79  tff(c_520, plain, (![A_95]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_95, A_95))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_516])).
% 15.35/8.79  tff(c_192, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.35/8.79  tff(c_222, plain, (![A_16, C_86]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_86))=k5_xboole_0(k1_xboole_0, C_86))), inference(superposition, [status(thm), theory('equality')], [c_18, c_192])).
% 15.35/8.79  tff(c_532, plain, (![A_95]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_95, A_95))=k5_xboole_0(k1_xboole_0, A_95))), inference(superposition, [status(thm), theory('equality')], [c_520, c_222])).
% 15.35/8.79  tff(c_543, plain, (![A_95]: (k5_xboole_0(k1_xboole_0, A_95)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_519, c_532])).
% 15.35/8.79  tff(c_313, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_18, c_192])).
% 15.35/8.79  tff(c_373, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_313])).
% 15.35/8.79  tff(c_669, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_543, c_373])).
% 15.35/8.79  tff(c_206, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k5_xboole_0(B_85, k5_xboole_0(A_84, B_85)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_192, c_18])).
% 15.35/8.79  tff(c_722, plain, (![A_103, C_104]: (k5_xboole_0(A_103, k5_xboole_0(A_103, C_104))=C_104)), inference(demodulation, [status(thm), theory('equality')], [c_543, c_222])).
% 15.35/8.79  tff(c_775, plain, (![B_85, A_84]: (k5_xboole_0(B_85, k5_xboole_0(A_84, B_85))=k5_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_206, c_722])).
% 15.35/8.79  tff(c_856, plain, (![B_108, A_109]: (k5_xboole_0(B_108, k5_xboole_0(A_109, B_108))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_669, c_775])).
% 15.35/8.79  tff(c_922, plain, (![A_5, B_6]: (k5_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_10, c_856])).
% 15.35/8.79  tff(c_16, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.35/8.79  tff(c_810, plain, (![A_105, C_106, B_107]: (r1_tarski(k5_xboole_0(A_105, C_106), B_107) | ~r1_tarski(C_106, B_107) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.35/8.79  tff(c_11026, plain, (![A_313, B_314, C_315, B_316]: (r1_tarski(k5_xboole_0(A_313, k5_xboole_0(B_314, C_315)), B_316) | ~r1_tarski(C_315, B_316) | ~r1_tarski(k5_xboole_0(A_313, B_314), B_316))), inference(superposition, [status(thm), theory('equality')], [c_16, c_810])).
% 15.35/8.79  tff(c_11306, plain, (![A_313, B_316, A_16]: (r1_tarski(k5_xboole_0(A_313, k1_xboole_0), B_316) | ~r1_tarski(A_16, B_316) | ~r1_tarski(k5_xboole_0(A_313, A_16), B_316))), inference(superposition, [status(thm), theory('equality')], [c_18, c_11026])).
% 15.35/8.79  tff(c_35937, plain, (![A_415, B_416, A_417]: (r1_tarski(A_415, B_416) | ~r1_tarski(A_417, B_416) | ~r1_tarski(k5_xboole_0(A_415, A_417), B_416))), inference(demodulation, [status(thm), theory('equality')], [c_669, c_11306])).
% 15.35/8.79  tff(c_36204, plain, (![A_418, A_419]: (r1_tarski(A_418, k5_xboole_0(A_418, A_419)) | ~r1_tarski(A_419, k5_xboole_0(A_418, A_419)))), inference(resolution, [status(thm)], [c_8, c_35937])).
% 15.35/8.79  tff(c_36344, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), k5_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))) | ~r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_922, c_36204])).
% 15.35/8.79  tff(c_39121, plain, (![A_453, B_454]: (r1_tarski(k3_xboole_0(A_453, B_454), A_453) | ~r1_tarski(k4_xboole_0(A_453, B_454), A_453))), inference(demodulation, [status(thm), theory('equality')], [c_922, c_36344])).
% 15.35/8.79  tff(c_39144, plain, (![B_8, C_9]: (r1_tarski(k3_xboole_0(B_8, C_9), B_8) | ~r1_tarski(B_8, B_8))), inference(resolution, [status(thm)], [c_12, c_39121])).
% 15.35/8.79  tff(c_39160, plain, (![B_8, C_9]: (r1_tarski(k3_xboole_0(B_8, C_9), B_8))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_39144])).
% 15.35/8.79  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.35/8.79  tff(c_639, plain, (![A_98, B_99, C_100]: (k9_subset_1(A_98, B_99, C_100)=k3_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.35/8.79  tff(c_644, plain, (![B_99]: (k9_subset_1('#skF_1', B_99, '#skF_3')=k3_xboole_0(B_99, '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_639])).
% 15.35/8.79  tff(c_1443, plain, (![A_125, B_126, C_127]: (m1_subset_1(k9_subset_1(A_125, B_126, C_127), k1_zfmisc_1(A_125)) | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.35/8.79  tff(c_1448, plain, (![B_99]: (m1_subset_1(k3_xboole_0(B_99, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_644, c_1443])).
% 15.35/8.79  tff(c_1454, plain, (![B_99]: (m1_subset_1(k3_xboole_0(B_99, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1448])).
% 15.35/8.79  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.35/8.79  tff(c_2395, plain, (![A_177, C_178, B_179]: (r1_tarski(k3_subset_1(A_177, C_178), k3_subset_1(A_177, B_179)) | ~r1_tarski(B_179, C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(A_177)) | ~m1_subset_1(B_179, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.35/8.79  tff(c_44, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.35/8.79  tff(c_1316, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_644, c_44])).
% 15.35/8.79  tff(c_2398, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2395, c_1316])).
% 15.35/8.79  tff(c_2403, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1454, c_48, c_2398])).
% 15.35/8.79  tff(c_39171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39160, c_2403])).
% 15.35/8.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/8.79  
% 15.35/8.79  Inference rules
% 15.35/8.79  ----------------------
% 15.35/8.79  #Ref     : 0
% 15.35/8.79  #Sup     : 10385
% 15.35/8.79  #Fact    : 0
% 15.35/8.79  #Define  : 0
% 15.35/8.79  #Split   : 0
% 15.35/8.79  #Chain   : 0
% 15.35/8.79  #Close   : 0
% 15.35/8.79  
% 15.35/8.79  Ordering : KBO
% 15.35/8.79  
% 15.35/8.79  Simplification rules
% 15.35/8.79  ----------------------
% 15.35/8.79  #Subsume      : 713
% 15.35/8.79  #Demod        : 14190
% 15.35/8.79  #Tautology    : 3687
% 15.35/8.79  #SimpNegUnit  : 0
% 15.35/8.79  #BackRed      : 13
% 15.35/8.79  
% 15.35/8.79  #Partial instantiations: 0
% 15.35/8.79  #Strategies tried      : 1
% 15.35/8.79  
% 15.35/8.79  Timing (in seconds)
% 15.35/8.79  ----------------------
% 15.35/8.79  Preprocessing        : 0.33
% 15.35/8.79  Parsing              : 0.18
% 15.35/8.79  CNF conversion       : 0.02
% 15.35/8.79  Main loop            : 7.65
% 15.35/8.79  Inferencing          : 1.06
% 15.35/8.79  Reduction            : 5.28
% 15.35/8.79  Demodulation         : 5.00
% 15.35/8.79  BG Simplification    : 0.18
% 15.35/8.79  Subsumption          : 0.91
% 15.35/8.79  Abstraction          : 0.27
% 15.35/8.79  MUC search           : 0.00
% 15.35/8.79  Cooper               : 0.00
% 15.35/8.79  Total                : 8.01
% 15.35/8.79  Index Insertion      : 0.00
% 15.35/8.80  Index Deletion       : 0.00
% 15.35/8.80  Index Matching       : 0.00
% 15.35/8.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
