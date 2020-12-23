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
% DateTime   : Thu Dec  3 09:55:49 EST 2020

% Result     : Theorem 39.72s
% Output     : CNFRefutation 39.76s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 202 expanded)
%              Number of leaves         :   36 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  137 ( 337 expanded)
%              Number of equality atoms :   23 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_101,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_373,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    ! [A_31] : k3_tarski(k1_zfmisc_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_200,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k3_tarski(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_206,plain,(
    ! [A_59,A_31] :
      ( r1_tarski(A_59,A_31)
      | ~ r2_hidden(A_59,k1_zfmisc_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_200])).

tff(c_377,plain,(
    ! [B_83,A_31] :
      ( r1_tarski(B_83,A_31)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_31))
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_373,c_206])).

tff(c_499,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_377])).

tff(c_512,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_499])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_511,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_499])).

tff(c_536,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,C_105)
      | ~ r1_tarski(B_106,C_105)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_587,plain,(
    ! [A_109] :
      ( r1_tarski(A_109,'#skF_1')
      | ~ r1_tarski(A_109,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_511,c_536])).

tff(c_603,plain,(
    ! [B_17] : r1_tarski(k4_xboole_0('#skF_3',B_17),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_587])).

tff(c_26,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_284,plain,(
    ! [B_74,A_75] :
      ( ~ r1_xboole_0(B_74,A_75)
      | ~ r1_tarski(B_74,A_75)
      | v1_xboole_0(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_851,plain,(
    ! [A_135,B_136] :
      ( ~ r1_tarski(k4_xboole_0(A_135,B_136),B_136)
      | v1_xboole_0(k4_xboole_0(A_135,B_136)) ) ),
    inference(resolution,[status(thm)],[c_26,c_284])).

tff(c_898,plain,(
    v1_xboole_0(k4_xboole_0('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_603,c_851])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1320,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_898,c_4])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1443,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_20])).

tff(c_1471,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1443])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_919,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,B_139) = k3_subset_1(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_931,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_919])).

tff(c_1156,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_20])).

tff(c_1175,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1156])).

tff(c_3493,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1175])).

tff(c_50,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_208,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(A_63,B_64)
      | ~ r1_tarski(A_63,k4_xboole_0(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,(
    ! [B_64,C_65,B_17] : r1_tarski(k4_xboole_0(k4_xboole_0(B_64,C_65),B_17),B_64) ),
    inference(resolution,[status(thm)],[c_18,c_208])).

tff(c_1182,plain,(
    ! [A_142,B_143,C_144] :
      ( r1_tarski(A_142,B_143)
      | ~ r1_xboole_0(A_142,C_144)
      | ~ r1_tarski(A_142,k2_xboole_0(B_143,C_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_31635,plain,(
    ! [B_619,C_620,C_621,B_622] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_619,C_620),C_621),B_622),B_619)
      | ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_619,C_620),C_621),B_622),C_620) ) ),
    inference(resolution,[status(thm)],[c_213,c_1182])).

tff(c_32208,plain,(
    ! [B_626,B_627,C_628] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_626,B_627),C_628),B_627),B_626) ),
    inference(resolution,[status(thm)],[c_26,c_31635])).

tff(c_33026,plain,(
    ! [A_635,B_636,C_637] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(A_635,B_636),C_637),A_635),B_636) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32208])).

tff(c_167294,plain,(
    ! [C_1448] : r1_tarski(k4_xboole_0(k4_xboole_0('#skF_1',C_1448),'#skF_3'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3493,c_33026])).

tff(c_56,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_190,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_56])).

tff(c_556,plain,(
    ! [A_104] :
      ( r1_tarski(A_104,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_104,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_190,c_536])).

tff(c_932,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_919])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3092,plain,(
    ! [A_192] :
      ( r1_xboole_0(A_192,'#skF_2')
      | ~ r1_tarski(A_192,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_8])).

tff(c_3127,plain,(
    ! [A_104] :
      ( r1_xboole_0(A_104,'#skF_2')
      | ~ r1_tarski(A_104,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_556,c_3092])).

tff(c_167431,plain,(
    ! [C_1449] : r1_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1',C_1449),'#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_167294,c_3127])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_xboole_0(B_5,A_4)
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167631,plain,(
    ! [C_1452] : r1_xboole_0('#skF_2',k4_xboole_0(k4_xboole_0('#skF_1',C_1452),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_167431,c_6])).

tff(c_1193,plain,(
    ! [A_142,A_18,B_19] :
      ( r1_tarski(A_142,A_18)
      | ~ r1_xboole_0(A_142,k4_xboole_0(B_19,A_18))
      | ~ r1_tarski(A_142,k2_xboole_0(A_18,B_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1182])).

tff(c_167637,plain,(
    ! [C_1452] :
      ( r1_tarski('#skF_2','#skF_3')
      | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_1452))) ) ),
    inference(resolution,[status(thm)],[c_167631,c_1193])).

tff(c_167713,plain,(
    ! [C_1453] : ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_1453))) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_167637])).

tff(c_167753,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_167713])).

tff(c_167775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_3493,c_167753])).

tff(c_167776,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_167777,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_168287,plain,(
    ! [A_1513,B_1514] :
      ( k4_xboole_0(A_1513,B_1514) = k3_subset_1(A_1513,B_1514)
      | ~ m1_subset_1(B_1514,k1_zfmisc_1(A_1513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_168299,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_168287])).

tff(c_168300,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_168287])).

tff(c_16,plain,(
    ! [C_15,B_14,A_13] :
      ( r1_tarski(k4_xboole_0(C_15,B_14),k4_xboole_0(C_15,A_13))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_176184,plain,(
    ! [B_1716] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_1716),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_1716) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168300,c_16])).

tff(c_176215,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_168299,c_176184])).

tff(c_176233,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167777,c_176215])).

tff(c_176235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167776,c_176233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.72/31.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.76/31.41  
% 39.76/31.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.76/31.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 39.76/31.41  
% 39.76/31.41  %Foreground sorts:
% 39.76/31.41  
% 39.76/31.41  
% 39.76/31.41  %Background operators:
% 39.76/31.41  
% 39.76/31.41  
% 39.76/31.41  %Foreground operators:
% 39.76/31.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.76/31.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 39.76/31.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 39.76/31.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 39.76/31.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.76/31.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.76/31.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 39.76/31.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 39.76/31.41  tff('#skF_2', type, '#skF_2': $i).
% 39.76/31.41  tff('#skF_3', type, '#skF_3': $i).
% 39.76/31.41  tff('#skF_1', type, '#skF_1': $i).
% 39.76/31.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.76/31.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.76/31.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 39.76/31.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.76/31.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.76/31.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 39.76/31.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 39.76/31.41  
% 39.76/31.43  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 39.76/31.43  tff(f_101, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 39.76/31.43  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 39.76/31.43  tff(f_81, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 39.76/31.43  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 39.76/31.43  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 39.76/31.43  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 39.76/31.43  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 39.76/31.43  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 39.76/31.43  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 39.76/31.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 39.76/31.43  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 39.76/31.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 39.76/31.43  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 39.76/31.43  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 39.76/31.43  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 39.76/31.43  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 39.76/31.43  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 39.76/31.43  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.76/31.43  tff(c_44, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.76/31.43  tff(c_373, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 39.76/31.43  tff(c_32, plain, (![A_31]: (k3_tarski(k1_zfmisc_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_81])).
% 39.76/31.43  tff(c_200, plain, (![A_59, B_60]: (r1_tarski(A_59, k3_tarski(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 39.76/31.43  tff(c_206, plain, (![A_59, A_31]: (r1_tarski(A_59, A_31) | ~r2_hidden(A_59, k1_zfmisc_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_200])).
% 39.76/31.43  tff(c_377, plain, (![B_83, A_31]: (r1_tarski(B_83, A_31) | ~m1_subset_1(B_83, k1_zfmisc_1(A_31)) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_373, c_206])).
% 39.76/31.43  tff(c_499, plain, (![B_100, A_101]: (r1_tarski(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)))), inference(negUnitSimplification, [status(thm)], [c_44, c_377])).
% 39.76/31.43  tff(c_512, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_499])).
% 39.76/31.43  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 39.76/31.43  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 39.76/31.43  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.76/31.43  tff(c_511, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_499])).
% 39.76/31.43  tff(c_536, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, C_105) | ~r1_tarski(B_106, C_105) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.76/31.43  tff(c_587, plain, (![A_109]: (r1_tarski(A_109, '#skF_1') | ~r1_tarski(A_109, '#skF_3'))), inference(resolution, [status(thm)], [c_511, c_536])).
% 39.76/31.43  tff(c_603, plain, (![B_17]: (r1_tarski(k4_xboole_0('#skF_3', B_17), '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_587])).
% 39.76/31.43  tff(c_26, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 39.76/31.43  tff(c_284, plain, (![B_74, A_75]: (~r1_xboole_0(B_74, A_75) | ~r1_tarski(B_74, A_75) | v1_xboole_0(B_74))), inference(cnfTransformation, [status(thm)], [f_65])).
% 39.76/31.43  tff(c_851, plain, (![A_135, B_136]: (~r1_tarski(k4_xboole_0(A_135, B_136), B_136) | v1_xboole_0(k4_xboole_0(A_135, B_136)))), inference(resolution, [status(thm)], [c_26, c_284])).
% 39.76/31.43  tff(c_898, plain, (v1_xboole_0(k4_xboole_0('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_603, c_851])).
% 39.76/31.43  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.76/31.43  tff(c_1320, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_898, c_4])).
% 39.76/31.43  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 39.76/31.43  tff(c_1443, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1320, c_20])).
% 39.76/31.43  tff(c_1471, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1443])).
% 39.76/31.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 39.76/31.43  tff(c_919, plain, (![A_138, B_139]: (k4_xboole_0(A_138, B_139)=k3_subset_1(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 39.76/31.43  tff(c_931, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_919])).
% 39.76/31.43  tff(c_1156, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))=k2_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_931, c_20])).
% 39.76/31.43  tff(c_1175, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))=k2_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1156])).
% 39.76/31.43  tff(c_3493, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1175])).
% 39.76/31.43  tff(c_50, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.76/31.43  tff(c_83, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 39.76/31.43  tff(c_208, plain, (![A_63, B_64, C_65]: (r1_tarski(A_63, B_64) | ~r1_tarski(A_63, k4_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.76/31.43  tff(c_213, plain, (![B_64, C_65, B_17]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_64, C_65), B_17), B_64))), inference(resolution, [status(thm)], [c_18, c_208])).
% 39.76/31.43  tff(c_1182, plain, (![A_142, B_143, C_144]: (r1_tarski(A_142, B_143) | ~r1_xboole_0(A_142, C_144) | ~r1_tarski(A_142, k2_xboole_0(B_143, C_144)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.76/31.43  tff(c_31635, plain, (![B_619, C_620, C_621, B_622]: (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_619, C_620), C_621), B_622), B_619) | ~r1_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_619, C_620), C_621), B_622), C_620))), inference(resolution, [status(thm)], [c_213, c_1182])).
% 39.76/31.43  tff(c_32208, plain, (![B_626, B_627, C_628]: (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(B_626, B_627), C_628), B_627), B_626))), inference(resolution, [status(thm)], [c_26, c_31635])).
% 39.76/31.43  tff(c_33026, plain, (![A_635, B_636, C_637]: (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(A_635, B_636), C_637), A_635), B_636))), inference(superposition, [status(thm), theory('equality')], [c_2, c_32208])).
% 39.76/31.43  tff(c_167294, plain, (![C_1448]: (r1_tarski(k4_xboole_0(k4_xboole_0('#skF_1', C_1448), '#skF_3'), k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3493, c_33026])).
% 39.76/31.43  tff(c_56, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.76/31.43  tff(c_190, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_83, c_56])).
% 39.76/31.43  tff(c_556, plain, (![A_104]: (r1_tarski(A_104, k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski(A_104, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_190, c_536])).
% 39.76/31.43  tff(c_932, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_919])).
% 39.76/31.43  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.76/31.43  tff(c_3092, plain, (![A_192]: (r1_xboole_0(A_192, '#skF_2') | ~r1_tarski(A_192, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_932, c_8])).
% 39.76/31.43  tff(c_3127, plain, (![A_104]: (r1_xboole_0(A_104, '#skF_2') | ~r1_tarski(A_104, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_556, c_3092])).
% 39.76/31.43  tff(c_167431, plain, (![C_1449]: (r1_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', C_1449), '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_167294, c_3127])).
% 39.76/31.43  tff(c_6, plain, (![B_5, A_4]: (r1_xboole_0(B_5, A_4) | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 39.76/31.43  tff(c_167631, plain, (![C_1452]: (r1_xboole_0('#skF_2', k4_xboole_0(k4_xboole_0('#skF_1', C_1452), '#skF_3')))), inference(resolution, [status(thm)], [c_167431, c_6])).
% 39.76/31.43  tff(c_1193, plain, (![A_142, A_18, B_19]: (r1_tarski(A_142, A_18) | ~r1_xboole_0(A_142, k4_xboole_0(B_19, A_18)) | ~r1_tarski(A_142, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1182])).
% 39.76/31.43  tff(c_167637, plain, (![C_1452]: (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_1452))))), inference(resolution, [status(thm)], [c_167631, c_1193])).
% 39.76/31.43  tff(c_167713, plain, (![C_1453]: (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_1453))))), inference(negUnitSimplification, [status(thm)], [c_83, c_167637])).
% 39.76/31.43  tff(c_167753, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_931, c_167713])).
% 39.76/31.43  tff(c_167775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_512, c_3493, c_167753])).
% 39.76/31.43  tff(c_167776, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 39.76/31.43  tff(c_167777, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 39.76/31.43  tff(c_168287, plain, (![A_1513, B_1514]: (k4_xboole_0(A_1513, B_1514)=k3_subset_1(A_1513, B_1514) | ~m1_subset_1(B_1514, k1_zfmisc_1(A_1513)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 39.76/31.43  tff(c_168299, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_168287])).
% 39.76/31.43  tff(c_168300, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_168287])).
% 39.76/31.43  tff(c_16, plain, (![C_15, B_14, A_13]: (r1_tarski(k4_xboole_0(C_15, B_14), k4_xboole_0(C_15, A_13)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 39.76/31.43  tff(c_176184, plain, (![B_1716]: (r1_tarski(k4_xboole_0('#skF_1', B_1716), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_1716))), inference(superposition, [status(thm), theory('equality')], [c_168300, c_16])).
% 39.76/31.43  tff(c_176215, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_168299, c_176184])).
% 39.76/31.43  tff(c_176233, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_167777, c_176215])).
% 39.76/31.43  tff(c_176235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167776, c_176233])).
% 39.76/31.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.76/31.43  
% 39.76/31.43  Inference rules
% 39.76/31.43  ----------------------
% 39.76/31.43  #Ref     : 0
% 39.76/31.43  #Sup     : 41892
% 39.76/31.43  #Fact    : 0
% 39.76/31.43  #Define  : 0
% 39.76/31.43  #Split   : 33
% 39.76/31.43  #Chain   : 0
% 39.76/31.43  #Close   : 0
% 39.76/31.43  
% 39.76/31.43  Ordering : KBO
% 39.76/31.43  
% 39.76/31.43  Simplification rules
% 39.76/31.43  ----------------------
% 39.76/31.43  #Subsume      : 13415
% 39.76/31.43  #Demod        : 39404
% 39.76/31.43  #Tautology    : 19248
% 39.76/31.43  #SimpNegUnit  : 449
% 39.76/31.43  #BackRed      : 32
% 39.76/31.43  
% 39.76/31.43  #Partial instantiations: 0
% 39.76/31.43  #Strategies tried      : 1
% 39.76/31.43  
% 39.76/31.43  Timing (in seconds)
% 39.76/31.43  ----------------------
% 39.76/31.43  Preprocessing        : 0.32
% 39.76/31.43  Parsing              : 0.18
% 39.76/31.43  CNF conversion       : 0.02
% 39.76/31.43  Main loop            : 30.33
% 39.76/31.43  Inferencing          : 3.02
% 39.76/31.43  Reduction            : 16.46
% 39.76/31.43  Demodulation         : 13.95
% 39.76/31.43  BG Simplification    : 0.25
% 39.76/31.43  Subsumption          : 9.47
% 39.76/31.43  Abstraction          : 0.40
% 39.76/31.43  MUC search           : 0.00
% 39.76/31.43  Cooper               : 0.00
% 39.76/31.43  Total                : 30.69
% 39.90/31.43  Index Insertion      : 0.00
% 39.90/31.43  Index Deletion       : 0.00
% 39.90/31.43  Index Matching       : 0.00
% 39.90/31.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
