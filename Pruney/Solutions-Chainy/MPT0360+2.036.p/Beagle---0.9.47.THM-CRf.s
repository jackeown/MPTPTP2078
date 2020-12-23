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
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 16.94s
% Output     : CNFRefutation 16.94s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 327 expanded)
%              Number of leaves         :   50 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 687 expanded)
%              Number of equality atoms :   25 ( 122 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_143,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_175,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_158,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_181,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_134,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_114,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_217,plain,(
    ! [B_156,A_157] :
      ( v1_xboole_0(B_156)
      | ~ m1_subset_1(B_156,A_157)
      | ~ v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_221,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_114,c_217])).

tff(c_222,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_339,plain,(
    ! [B_177,A_178] :
      ( r2_hidden(B_177,A_178)
      | ~ m1_subset_1(B_177,A_178)
      | v1_xboole_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    ! [C_61,A_57] :
      ( r1_tarski(C_61,A_57)
      | ~ r2_hidden(C_61,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5552,plain,(
    ! [B_422,A_423] :
      ( r1_tarski(B_422,A_423)
      | ~ m1_subset_1(B_422,k1_zfmisc_1(A_423))
      | v1_xboole_0(k1_zfmisc_1(A_423)) ) ),
    inference(resolution,[status(thm)],[c_339,c_50])).

tff(c_5579,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_114,c_5552])).

tff(c_5593,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_5579])).

tff(c_52,plain,(
    ! [C_61,A_57] :
      ( r2_hidden(C_61,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_61,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_84,plain,(
    ! [A_121] : k3_tarski(k1_zfmisc_1(A_121)) = A_121 ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_112,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_62,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,k3_tarski(B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_522,plain,(
    ! [A_199,C_200,B_201] :
      ( r1_tarski(A_199,C_200)
      | ~ r1_tarski(B_201,C_200)
      | ~ r1_tarski(A_199,B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5059,plain,(
    ! [A_404,B_405,A_406] :
      ( r1_tarski(A_404,k3_tarski(B_405))
      | ~ r1_tarski(A_404,A_406)
      | ~ r2_hidden(A_406,B_405) ) ),
    inference(resolution,[status(thm)],[c_62,c_522])).

tff(c_5127,plain,(
    ! [B_407] :
      ( r1_tarski('#skF_9',k3_tarski(B_407))
      | ~ r2_hidden('#skF_10',B_407) ) ),
    inference(resolution,[status(thm)],[c_112,c_5059])).

tff(c_5162,plain,(
    ! [A_409] :
      ( r1_tarski('#skF_9',A_409)
      | ~ r2_hidden('#skF_10',k1_zfmisc_1(A_409)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_5127])).

tff(c_5171,plain,(
    ! [A_57] :
      ( r1_tarski('#skF_9',A_57)
      | ~ r1_tarski('#skF_10',A_57) ) ),
    inference(resolution,[status(thm)],[c_52,c_5162])).

tff(c_5605,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_5593,c_5171])).

tff(c_370,plain,(
    ! [B_179,A_180] :
      ( m1_subset_1(B_179,A_180)
      | ~ r2_hidden(B_179,A_180)
      | v1_xboole_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_389,plain,(
    ! [C_61,A_57] :
      ( m1_subset_1(C_61,k1_zfmisc_1(A_57))
      | v1_xboole_0(k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_61,A_57) ) ),
    inference(resolution,[status(thm)],[c_52,c_370])).

tff(c_108,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_110,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_4213,plain,(
    ! [A_362,C_363,B_364] :
      ( r1_tarski(k3_subset_1(A_362,C_363),k3_subset_1(A_362,B_364))
      | ~ r1_tarski(B_364,C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(A_362))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(A_362)) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32393,plain,(
    ! [A_896,A_897,B_898,C_899] :
      ( r1_tarski(A_896,k3_subset_1(A_897,B_898))
      | ~ r1_tarski(A_896,k3_subset_1(A_897,C_899))
      | ~ r1_tarski(B_898,C_899)
      | ~ m1_subset_1(C_899,k1_zfmisc_1(A_897))
      | ~ m1_subset_1(B_898,k1_zfmisc_1(A_897)) ) ),
    inference(resolution,[status(thm)],[c_4213,c_16])).

tff(c_32620,plain,(
    ! [B_898] :
      ( r1_tarski('#skF_9',k3_subset_1('#skF_8',B_898))
      | ~ r1_tarski(B_898,'#skF_10')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8'))
      | ~ m1_subset_1(B_898,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_110,c_32393])).

tff(c_32744,plain,(
    ! [B_900] :
      ( r1_tarski('#skF_9',k3_subset_1('#skF_8',B_900))
      | ~ r1_tarski(B_900,'#skF_10')
      | ~ m1_subset_1(B_900,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_32620])).

tff(c_94,plain,(
    ! [A_124] : k1_subset_1(A_124) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_106,plain,(
    ! [A_133,B_134] :
      ( k1_subset_1(A_133) = B_134
      | ~ r1_tarski(B_134,k3_subset_1(A_133,B_134))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_116,plain,(
    ! [B_134,A_133] :
      ( k1_xboole_0 = B_134
      | ~ r1_tarski(B_134,k3_subset_1(A_133,B_134))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_106])).

tff(c_32758,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_10')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_32744,c_116])).

tff(c_32782,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_32758])).

tff(c_32783,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_32782])).

tff(c_32793,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_8'))
    | ~ r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_389,c_32783])).

tff(c_32799,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5605,c_32793])).

tff(c_32801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_32799])).

tff(c_32803,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_32802,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( ~ v1_xboole_0(B_22)
      | B_22 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32860,plain,(
    ! [A_905] :
      ( A_905 = '#skF_10'
      | ~ v1_xboole_0(A_905) ) ),
    inference(resolution,[status(thm)],[c_32802,c_28])).

tff(c_32867,plain,(
    k1_zfmisc_1('#skF_8') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32803,c_32860])).

tff(c_32879,plain,(
    k3_tarski('#skF_10') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_32867,c_84])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32810,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32802,c_10])).

tff(c_76,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32819,plain,(
    k3_tarski('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32810,c_32810,c_76])).

tff(c_32889,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32879,c_32819])).

tff(c_32908,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32889,c_112])).

tff(c_18,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32817,plain,(
    ! [A_16] : r1_tarski('#skF_10',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32810,c_18])).

tff(c_32903,plain,(
    ! [A_16] : r1_tarski('#skF_8',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32889,c_32817])).

tff(c_33342,plain,(
    ! [A_956,C_957,B_958] :
      ( r1_tarski(A_956,C_957)
      | ~ r1_tarski(B_958,C_957)
      | ~ r1_tarski(A_956,B_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33364,plain,(
    ! [A_959,A_960] :
      ( r1_tarski(A_959,A_960)
      | ~ r1_tarski(A_959,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_32903,c_33342])).

tff(c_33386,plain,(
    ! [A_960] : r1_tarski('#skF_9',A_960) ),
    inference(resolution,[status(thm)],[c_32908,c_33364])).

tff(c_32876,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_10')
      | ~ r1_tarski(C_61,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32867,c_52])).

tff(c_33031,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_8')
      | ~ r1_tarski(C_61,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32889,c_32876])).

tff(c_33387,plain,(
    ! [C_961,B_962,A_963] :
      ( r2_hidden(C_961,B_962)
      | ~ r2_hidden(C_961,A_963)
      | ~ r1_tarski(A_963,B_962) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33397,plain,(
    ! [C_61,B_962] :
      ( r2_hidden(C_61,B_962)
      | ~ r1_tarski('#skF_8',B_962)
      | ~ r1_tarski(C_61,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_33031,c_33387])).

tff(c_33454,plain,(
    ! [C_966,B_967] :
      ( r2_hidden(C_966,B_967)
      | ~ r1_tarski(C_966,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32903,c_33397])).

tff(c_80,plain,(
    ! [C_120,B_119] : ~ r2_hidden(C_120,k4_xboole_0(B_119,k1_tarski(C_120))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_33518,plain,(
    ! [C_969] : ~ r1_tarski(C_969,'#skF_8') ),
    inference(resolution,[status(thm)],[c_33454,c_80])).

tff(c_33537,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_33386,c_33518])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.94/8.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.94/8.41  
% 16.94/8.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.94/8.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_7 > #skF_1 > #skF_4
% 16.94/8.41  
% 16.94/8.41  %Foreground sorts:
% 16.94/8.41  
% 16.94/8.41  
% 16.94/8.41  %Background operators:
% 16.94/8.41  
% 16.94/8.41  
% 16.94/8.41  %Foreground operators:
% 16.94/8.41  tff('#skF_5', type, '#skF_5': $i > $i).
% 16.94/8.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.94/8.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.94/8.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.94/8.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.94/8.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.94/8.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.94/8.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.94/8.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.94/8.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.94/8.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.94/8.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.94/8.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.94/8.41  tff('#skF_10', type, '#skF_10': $i).
% 16.94/8.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.94/8.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.94/8.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.94/8.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.94/8.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.94/8.41  tff('#skF_9', type, '#skF_9': $i).
% 16.94/8.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.94/8.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.94/8.41  tff('#skF_8', type, '#skF_8': $i).
% 16.94/8.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.94/8.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.94/8.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.94/8.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 16.94/8.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.94/8.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.94/8.41  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.94/8.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.94/8.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.94/8.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.94/8.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.94/8.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.94/8.41  
% 16.94/8.43  tff(f_190, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 16.94/8.43  tff(f_156, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 16.94/8.43  tff(f_113, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 16.94/8.43  tff(f_143, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 16.94/8.43  tff(f_117, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 16.94/8.43  tff(f_54, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.94/8.43  tff(f_175, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 16.94/8.43  tff(f_158, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 16.94/8.43  tff(f_181, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 16.94/8.43  tff(f_86, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 16.94/8.43  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 16.94/8.43  tff(f_134, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 16.94/8.43  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.94/8.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.94/8.43  tff(f_141, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 16.94/8.43  tff(c_114, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 16.94/8.43  tff(c_217, plain, (![B_156, A_157]: (v1_xboole_0(B_156) | ~m1_subset_1(B_156, A_157) | ~v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.94/8.43  tff(c_221, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_114, c_217])).
% 16.94/8.43  tff(c_222, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_221])).
% 16.94/8.43  tff(c_339, plain, (![B_177, A_178]: (r2_hidden(B_177, A_178) | ~m1_subset_1(B_177, A_178) | v1_xboole_0(A_178))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.94/8.43  tff(c_50, plain, (![C_61, A_57]: (r1_tarski(C_61, A_57) | ~r2_hidden(C_61, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.94/8.43  tff(c_5552, plain, (![B_422, A_423]: (r1_tarski(B_422, A_423) | ~m1_subset_1(B_422, k1_zfmisc_1(A_423)) | v1_xboole_0(k1_zfmisc_1(A_423)))), inference(resolution, [status(thm)], [c_339, c_50])).
% 16.94/8.43  tff(c_5579, plain, (r1_tarski('#skF_10', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_114, c_5552])).
% 16.94/8.43  tff(c_5593, plain, (r1_tarski('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_222, c_5579])).
% 16.94/8.43  tff(c_52, plain, (![C_61, A_57]: (r2_hidden(C_61, k1_zfmisc_1(A_57)) | ~r1_tarski(C_61, A_57))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.94/8.43  tff(c_84, plain, (![A_121]: (k3_tarski(k1_zfmisc_1(A_121))=A_121)), inference(cnfTransformation, [status(thm)], [f_143])).
% 16.94/8.43  tff(c_112, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_190])).
% 16.94/8.43  tff(c_62, plain, (![A_62, B_63]: (r1_tarski(A_62, k3_tarski(B_63)) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.94/8.43  tff(c_522, plain, (![A_199, C_200, B_201]: (r1_tarski(A_199, C_200) | ~r1_tarski(B_201, C_200) | ~r1_tarski(A_199, B_201))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.94/8.43  tff(c_5059, plain, (![A_404, B_405, A_406]: (r1_tarski(A_404, k3_tarski(B_405)) | ~r1_tarski(A_404, A_406) | ~r2_hidden(A_406, B_405))), inference(resolution, [status(thm)], [c_62, c_522])).
% 16.94/8.43  tff(c_5127, plain, (![B_407]: (r1_tarski('#skF_9', k3_tarski(B_407)) | ~r2_hidden('#skF_10', B_407))), inference(resolution, [status(thm)], [c_112, c_5059])).
% 16.94/8.43  tff(c_5162, plain, (![A_409]: (r1_tarski('#skF_9', A_409) | ~r2_hidden('#skF_10', k1_zfmisc_1(A_409)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_5127])).
% 16.94/8.43  tff(c_5171, plain, (![A_57]: (r1_tarski('#skF_9', A_57) | ~r1_tarski('#skF_10', A_57))), inference(resolution, [status(thm)], [c_52, c_5162])).
% 16.94/8.43  tff(c_5605, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_5593, c_5171])).
% 16.94/8.43  tff(c_370, plain, (![B_179, A_180]: (m1_subset_1(B_179, A_180) | ~r2_hidden(B_179, A_180) | v1_xboole_0(A_180))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.94/8.43  tff(c_389, plain, (![C_61, A_57]: (m1_subset_1(C_61, k1_zfmisc_1(A_57)) | v1_xboole_0(k1_zfmisc_1(A_57)) | ~r1_tarski(C_61, A_57))), inference(resolution, [status(thm)], [c_52, c_370])).
% 16.94/8.43  tff(c_108, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_190])).
% 16.94/8.43  tff(c_110, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 16.94/8.43  tff(c_4213, plain, (![A_362, C_363, B_364]: (r1_tarski(k3_subset_1(A_362, C_363), k3_subset_1(A_362, B_364)) | ~r1_tarski(B_364, C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(A_362)) | ~m1_subset_1(B_364, k1_zfmisc_1(A_362)))), inference(cnfTransformation, [status(thm)], [f_175])).
% 16.94/8.43  tff(c_16, plain, (![A_13, C_15, B_14]: (r1_tarski(A_13, C_15) | ~r1_tarski(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.94/8.43  tff(c_32393, plain, (![A_896, A_897, B_898, C_899]: (r1_tarski(A_896, k3_subset_1(A_897, B_898)) | ~r1_tarski(A_896, k3_subset_1(A_897, C_899)) | ~r1_tarski(B_898, C_899) | ~m1_subset_1(C_899, k1_zfmisc_1(A_897)) | ~m1_subset_1(B_898, k1_zfmisc_1(A_897)))), inference(resolution, [status(thm)], [c_4213, c_16])).
% 16.94/8.43  tff(c_32620, plain, (![B_898]: (r1_tarski('#skF_9', k3_subset_1('#skF_8', B_898)) | ~r1_tarski(B_898, '#skF_10') | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8')) | ~m1_subset_1(B_898, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_110, c_32393])).
% 16.94/8.43  tff(c_32744, plain, (![B_900]: (r1_tarski('#skF_9', k3_subset_1('#skF_8', B_900)) | ~r1_tarski(B_900, '#skF_10') | ~m1_subset_1(B_900, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_32620])).
% 16.94/8.43  tff(c_94, plain, (![A_124]: (k1_subset_1(A_124)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_158])).
% 16.94/8.43  tff(c_106, plain, (![A_133, B_134]: (k1_subset_1(A_133)=B_134 | ~r1_tarski(B_134, k3_subset_1(A_133, B_134)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_181])).
% 16.94/8.43  tff(c_116, plain, (![B_134, A_133]: (k1_xboole_0=B_134 | ~r1_tarski(B_134, k3_subset_1(A_133, B_134)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_106])).
% 16.94/8.43  tff(c_32758, plain, (k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_10') | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_32744, c_116])).
% 16.94/8.43  tff(c_32782, plain, (k1_xboole_0='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_32758])).
% 16.94/8.43  tff(c_32783, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_108, c_32782])).
% 16.94/8.43  tff(c_32793, plain, (v1_xboole_0(k1_zfmisc_1('#skF_8')) | ~r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_389, c_32783])).
% 16.94/8.43  tff(c_32799, plain, (v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5605, c_32793])).
% 16.94/8.43  tff(c_32801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_32799])).
% 16.94/8.43  tff(c_32803, plain, (v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitRight, [status(thm)], [c_221])).
% 16.94/8.43  tff(c_32802, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_221])).
% 16.94/8.43  tff(c_28, plain, (![B_22, A_21]: (~v1_xboole_0(B_22) | B_22=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.94/8.43  tff(c_32860, plain, (![A_905]: (A_905='#skF_10' | ~v1_xboole_0(A_905))), inference(resolution, [status(thm)], [c_32802, c_28])).
% 16.94/8.43  tff(c_32867, plain, (k1_zfmisc_1('#skF_8')='#skF_10'), inference(resolution, [status(thm)], [c_32803, c_32860])).
% 16.94/8.43  tff(c_32879, plain, (k3_tarski('#skF_10')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_32867, c_84])).
% 16.94/8.43  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.94/8.43  tff(c_32810, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_32802, c_10])).
% 16.94/8.43  tff(c_76, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_134])).
% 16.94/8.43  tff(c_32819, plain, (k3_tarski('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_32810, c_32810, c_76])).
% 16.94/8.43  tff(c_32889, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32879, c_32819])).
% 16.94/8.43  tff(c_32908, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32889, c_112])).
% 16.94/8.43  tff(c_18, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.94/8.43  tff(c_32817, plain, (![A_16]: (r1_tarski('#skF_10', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_32810, c_18])).
% 16.94/8.43  tff(c_32903, plain, (![A_16]: (r1_tarski('#skF_8', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_32889, c_32817])).
% 16.94/8.43  tff(c_33342, plain, (![A_956, C_957, B_958]: (r1_tarski(A_956, C_957) | ~r1_tarski(B_958, C_957) | ~r1_tarski(A_956, B_958))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.94/8.43  tff(c_33364, plain, (![A_959, A_960]: (r1_tarski(A_959, A_960) | ~r1_tarski(A_959, '#skF_8'))), inference(resolution, [status(thm)], [c_32903, c_33342])).
% 16.94/8.43  tff(c_33386, plain, (![A_960]: (r1_tarski('#skF_9', A_960))), inference(resolution, [status(thm)], [c_32908, c_33364])).
% 16.94/8.43  tff(c_32876, plain, (![C_61]: (r2_hidden(C_61, '#skF_10') | ~r1_tarski(C_61, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_32867, c_52])).
% 16.94/8.43  tff(c_33031, plain, (![C_61]: (r2_hidden(C_61, '#skF_8') | ~r1_tarski(C_61, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32889, c_32876])).
% 16.94/8.43  tff(c_33387, plain, (![C_961, B_962, A_963]: (r2_hidden(C_961, B_962) | ~r2_hidden(C_961, A_963) | ~r1_tarski(A_963, B_962))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.94/8.43  tff(c_33397, plain, (![C_61, B_962]: (r2_hidden(C_61, B_962) | ~r1_tarski('#skF_8', B_962) | ~r1_tarski(C_61, '#skF_8'))), inference(resolution, [status(thm)], [c_33031, c_33387])).
% 16.94/8.43  tff(c_33454, plain, (![C_966, B_967]: (r2_hidden(C_966, B_967) | ~r1_tarski(C_966, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32903, c_33397])).
% 16.94/8.43  tff(c_80, plain, (![C_120, B_119]: (~r2_hidden(C_120, k4_xboole_0(B_119, k1_tarski(C_120))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.94/8.43  tff(c_33518, plain, (![C_969]: (~r1_tarski(C_969, '#skF_8'))), inference(resolution, [status(thm)], [c_33454, c_80])).
% 16.94/8.43  tff(c_33537, plain, $false, inference(resolution, [status(thm)], [c_33386, c_33518])).
% 16.94/8.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.94/8.43  
% 16.94/8.43  Inference rules
% 16.94/8.43  ----------------------
% 16.94/8.43  #Ref     : 0
% 16.94/8.43  #Sup     : 7812
% 16.94/8.43  #Fact    : 0
% 16.94/8.43  #Define  : 0
% 16.94/8.43  #Split   : 51
% 16.94/8.43  #Chain   : 0
% 16.94/8.43  #Close   : 0
% 16.94/8.43  
% 16.94/8.43  Ordering : KBO
% 16.94/8.43  
% 16.94/8.43  Simplification rules
% 16.94/8.43  ----------------------
% 16.94/8.43  #Subsume      : 1449
% 16.94/8.43  #Demod        : 4103
% 16.94/8.43  #Tautology    : 1880
% 16.94/8.43  #SimpNegUnit  : 246
% 16.94/8.43  #BackRed      : 399
% 16.94/8.43  
% 16.94/8.43  #Partial instantiations: 0
% 16.94/8.43  #Strategies tried      : 1
% 16.94/8.43  
% 16.94/8.43  Timing (in seconds)
% 16.94/8.43  ----------------------
% 16.94/8.43  Preprocessing        : 0.39
% 16.94/8.43  Parsing              : 0.21
% 16.94/8.43  CNF conversion       : 0.03
% 16.94/8.43  Main loop            : 7.24
% 16.94/8.43  Inferencing          : 1.30
% 16.94/8.43  Reduction            : 3.25
% 17.18/8.43  Demodulation         : 2.55
% 17.18/8.43  BG Simplification    : 0.13
% 17.18/8.43  Subsumption          : 2.04
% 17.18/8.43  Abstraction          : 0.16
% 17.18/8.43  MUC search           : 0.00
% 17.18/8.43  Cooper               : 0.00
% 17.18/8.43  Total                : 7.67
% 17.18/8.43  Index Insertion      : 0.00
% 17.18/8.43  Index Deletion       : 0.00
% 17.18/8.43  Index Matching       : 0.00
% 17.18/8.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
