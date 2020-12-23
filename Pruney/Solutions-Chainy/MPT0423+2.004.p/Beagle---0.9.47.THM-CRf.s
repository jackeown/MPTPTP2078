%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:52 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 142 expanded)
%              Number of leaves         :   48 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 224 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_76,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_110,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B = k1_tarski(A)
         => k7_setfam_1(A,B) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_78,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_115,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

tff(c_106,plain,(
    ! [A_57] : ~ v1_xboole_0(k1_zfmisc_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    ! [A_42] : k1_subset_1(A_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ! [A_56] : m1_subset_1(k1_subset_1(A_56),k1_zfmisc_1(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_132,plain,(
    ! [A_56] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_104])).

tff(c_40,plain,(
    ! [B_41,A_40] :
      ( r2_hidden(B_41,A_40)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_126,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_28,plain,(
    ! [B_37] : r1_tarski(k1_tarski(B_37),k1_tarski(B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_238,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,B_94)
      | ~ r1_tarski(k1_tarski(A_93),B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [B_37] : r2_hidden(B_37,k1_tarski(B_37)) ),
    inference(resolution,[status(thm)],[c_28,c_238])).

tff(c_110,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k1_tarski(A_59),k1_zfmisc_1(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_108,plain,(
    ! [A_58] : k3_subset_1(A_58,k1_subset_1(A_58)) = k2_subset_1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_131,plain,(
    ! [A_58] : k3_subset_1(A_58,k1_subset_1(A_58)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_108])).

tff(c_133,plain,(
    ! [A_58] : k3_subset_1(A_58,k1_xboole_0) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_131])).

tff(c_1491,plain,(
    ! [A_347,C_348,B_349] :
      ( r2_hidden(k3_subset_1(A_347,C_348),k7_setfam_1(A_347,B_349))
      | ~ r2_hidden(C_348,B_349)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(A_347))
      | ~ m1_subset_1(B_349,k1_zfmisc_1(k1_zfmisc_1(A_347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1509,plain,(
    ! [A_58,B_349] :
      ( r2_hidden(A_58,k7_setfam_1(A_58,B_349))
      | ~ r2_hidden(k1_xboole_0,B_349)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_349,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1491])).

tff(c_2301,plain,(
    ! [A_643,B_644] :
      ( r2_hidden(A_643,k7_setfam_1(A_643,B_644))
      | ~ r2_hidden(k1_xboole_0,B_644)
      | ~ m1_subset_1(B_644,k1_zfmisc_1(k1_zfmisc_1(A_643))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1509])).

tff(c_3071,plain,(
    ! [A_776,A_777] :
      ( r2_hidden(A_776,k7_setfam_1(A_776,k1_tarski(A_777)))
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_777))
      | ~ r2_hidden(A_777,k1_zfmisc_1(A_776)) ) ),
    inference(resolution,[status(thm)],[c_110,c_2301])).

tff(c_128,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_220,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_tarski(A_88),B_89)
      | ~ r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_4',B_89)
      | ~ r2_hidden('#skF_3',B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_220])).

tff(c_3086,plain,(
    ! [A_777] :
      ( r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_777)))
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_777))
      | ~ r2_hidden(A_777,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3071,c_223])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_353,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_362,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_353])).

tff(c_365,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_362])).

tff(c_211,plain,(
    ! [B_87] : k4_xboole_0(k1_tarski(B_87),k1_tarski(B_87)) != k1_tarski(B_87) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_214,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_211])).

tff(c_218,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_128,c_214])).

tff(c_383,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_218])).

tff(c_130,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_661,plain,(
    ! [A_165,B_166] :
      ( k7_setfam_1(A_165,B_166) != k1_xboole_0
      | k1_xboole_0 = B_166
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k1_zfmisc_1(A_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_676,plain,
    ( k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_130,c_661])).

tff(c_693,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_383,c_676])).

tff(c_112,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k7_setfam_1(A_61,B_62),k1_zfmisc_1(k1_zfmisc_1(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_800,plain,(
    ! [A_183,B_184] :
      ( k7_setfam_1(A_183,k7_setfam_1(A_183,B_184)) = B_184
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(A_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_820,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_130,c_800])).

tff(c_1594,plain,(
    ! [C_384,B_385,A_386] :
      ( r2_hidden(C_384,B_385)
      | ~ r2_hidden(k3_subset_1(A_386,C_384),k7_setfam_1(A_386,B_385))
      | ~ m1_subset_1(C_384,k1_zfmisc_1(A_386))
      | ~ m1_subset_1(B_385,k1_zfmisc_1(k1_zfmisc_1(A_386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1609,plain,(
    ! [C_384] :
      ( r2_hidden(C_384,k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(k3_subset_1('#skF_3',C_384),'#skF_4')
      | ~ m1_subset_1(C_384,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_1594])).

tff(c_2186,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1609])).

tff(c_2189,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_112,c_2186])).

tff(c_2196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_2189])).

tff(c_2198,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_1720,plain,(
    ! [B_413,C_414,A_415] :
      ( r1_tarski(B_413,C_414)
      | ~ r1_tarski(k7_setfam_1(A_415,B_413),k7_setfam_1(A_415,C_414))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k1_zfmisc_1(A_415)))
      | ~ m1_subset_1(B_413,k1_zfmisc_1(k1_zfmisc_1(A_415))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1741,plain,(
    ! [C_414] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),C_414)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',C_414))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_1720])).

tff(c_2422,plain,(
    ! [C_656] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),C_656)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',C_656))
      | ~ m1_subset_1(C_656,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_1741])).

tff(c_3671,plain,(
    ! [A_861] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),k1_tarski(A_861))
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_861)))
      | ~ r2_hidden(A_861,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_110,c_2422])).

tff(c_26,plain,(
    ! [B_37,A_36] :
      ( k1_tarski(B_37) = A_36
      | k1_xboole_0 = A_36
      | ~ r1_tarski(A_36,k1_tarski(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3674,plain,(
    ! [A_861] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_861)
      | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_861)))
      | ~ r2_hidden(A_861,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3671,c_26])).

tff(c_3684,plain,(
    ! [A_871] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_871)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_871)))
      | ~ r2_hidden(A_871,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_693,c_3674])).

tff(c_3697,plain,(
    ! [A_872] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_872)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_872))
      | ~ r2_hidden(A_872,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3086,c_3684])).

tff(c_3703,plain,
    ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_249,c_3697])).

tff(c_3709,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_3703])).

tff(c_3713,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_3709])).

tff(c_3716,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_3713])).

tff(c_3718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.27  
% 6.57/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.28  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.57/2.28  
% 6.57/2.28  %Foreground sorts:
% 6.57/2.28  
% 6.57/2.28  
% 6.57/2.28  %Background operators:
% 6.57/2.28  
% 6.57/2.28  
% 6.57/2.28  %Foreground operators:
% 6.57/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.57/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.57/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.57/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.57/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.57/2.28  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 6.57/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.57/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.57/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.57/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.57/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.57/2.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.57/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.57/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.57/2.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.57/2.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.57/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.57/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.57/2.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.57/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.57/2.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.57/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.57/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.57/2.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.57/2.28  
% 6.57/2.29  tff(f_113, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.57/2.29  tff(f_76, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 6.57/2.29  tff(f_110, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 6.57/2.29  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.57/2.29  tff(f_162, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((B = k1_tarski(A)) => (k7_setfam_1(A, B) = k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_setfam_1)).
% 6.57/2.29  tff(f_55, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.57/2.29  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.57/2.29  tff(f_119, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 6.57/2.29  tff(f_78, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.57/2.29  tff(f_115, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 6.57/2.29  tff(f_146, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 6.57/2.29  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.57/2.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.57/2.29  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.57/2.29  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.57/2.29  tff(f_137, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 6.57/2.29  tff(f_123, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 6.57/2.29  tff(f_127, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 6.57/2.29  tff(f_155, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 6.57/2.29  tff(c_106, plain, (![A_57]: (~v1_xboole_0(k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.57/2.29  tff(c_46, plain, (![A_42]: (k1_subset_1(A_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.57/2.29  tff(c_104, plain, (![A_56]: (m1_subset_1(k1_subset_1(A_56), k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.57/2.29  tff(c_132, plain, (![A_56]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_56)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_104])).
% 6.57/2.29  tff(c_40, plain, (![B_41, A_40]: (r2_hidden(B_41, A_40) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.57/2.29  tff(c_126, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.57/2.29  tff(c_28, plain, (![B_37]: (r1_tarski(k1_tarski(B_37), k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.57/2.29  tff(c_238, plain, (![A_93, B_94]: (r2_hidden(A_93, B_94) | ~r1_tarski(k1_tarski(A_93), B_94))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.57/2.29  tff(c_249, plain, (![B_37]: (r2_hidden(B_37, k1_tarski(B_37)))), inference(resolution, [status(thm)], [c_28, c_238])).
% 6.57/2.29  tff(c_110, plain, (![A_59, B_60]: (m1_subset_1(k1_tarski(A_59), k1_zfmisc_1(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.57/2.29  tff(c_48, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.57/2.29  tff(c_108, plain, (![A_58]: (k3_subset_1(A_58, k1_subset_1(A_58))=k2_subset_1(A_58))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.57/2.29  tff(c_131, plain, (![A_58]: (k3_subset_1(A_58, k1_subset_1(A_58))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_108])).
% 6.57/2.29  tff(c_133, plain, (![A_58]: (k3_subset_1(A_58, k1_xboole_0)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_131])).
% 6.57/2.29  tff(c_1491, plain, (![A_347, C_348, B_349]: (r2_hidden(k3_subset_1(A_347, C_348), k7_setfam_1(A_347, B_349)) | ~r2_hidden(C_348, B_349) | ~m1_subset_1(C_348, k1_zfmisc_1(A_347)) | ~m1_subset_1(B_349, k1_zfmisc_1(k1_zfmisc_1(A_347))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.57/2.29  tff(c_1509, plain, (![A_58, B_349]: (r2_hidden(A_58, k7_setfam_1(A_58, B_349)) | ~r2_hidden(k1_xboole_0, B_349) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_349, k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1491])).
% 6.57/2.29  tff(c_2301, plain, (![A_643, B_644]: (r2_hidden(A_643, k7_setfam_1(A_643, B_644)) | ~r2_hidden(k1_xboole_0, B_644) | ~m1_subset_1(B_644, k1_zfmisc_1(k1_zfmisc_1(A_643))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1509])).
% 6.57/2.29  tff(c_3071, plain, (![A_776, A_777]: (r2_hidden(A_776, k7_setfam_1(A_776, k1_tarski(A_777))) | ~r2_hidden(k1_xboole_0, k1_tarski(A_777)) | ~r2_hidden(A_777, k1_zfmisc_1(A_776)))), inference(resolution, [status(thm)], [c_110, c_2301])).
% 6.57/2.29  tff(c_128, plain, (k1_tarski('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.57/2.29  tff(c_220, plain, (![A_88, B_89]: (r1_tarski(k1_tarski(A_88), B_89) | ~r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.57/2.29  tff(c_223, plain, (![B_89]: (r1_tarski('#skF_4', B_89) | ~r2_hidden('#skF_3', B_89))), inference(superposition, [status(thm), theory('equality')], [c_128, c_220])).
% 6.57/2.29  tff(c_3086, plain, (![A_777]: (r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_777))) | ~r2_hidden(k1_xboole_0, k1_tarski(A_777)) | ~r2_hidden(A_777, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_3071, c_223])).
% 6.57/2.29  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.29  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.57/2.29  tff(c_353, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.57/2.29  tff(c_362, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_353])).
% 6.57/2.29  tff(c_365, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_362])).
% 6.57/2.29  tff(c_211, plain, (![B_87]: (k4_xboole_0(k1_tarski(B_87), k1_tarski(B_87))!=k1_tarski(B_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.57/2.29  tff(c_214, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128, c_211])).
% 6.57/2.29  tff(c_218, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_128, c_214])).
% 6.57/2.29  tff(c_383, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_218])).
% 6.57/2.29  tff(c_130, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.57/2.29  tff(c_661, plain, (![A_165, B_166]: (k7_setfam_1(A_165, B_166)!=k1_xboole_0 | k1_xboole_0=B_166 | ~m1_subset_1(B_166, k1_zfmisc_1(k1_zfmisc_1(A_165))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.57/2.29  tff(c_676, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_130, c_661])).
% 6.57/2.29  tff(c_693, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_383, c_676])).
% 6.57/2.29  tff(c_112, plain, (![A_61, B_62]: (m1_subset_1(k7_setfam_1(A_61, B_62), k1_zfmisc_1(k1_zfmisc_1(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.57/2.29  tff(c_800, plain, (![A_183, B_184]: (k7_setfam_1(A_183, k7_setfam_1(A_183, B_184))=B_184 | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(A_183))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.57/2.29  tff(c_820, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_130, c_800])).
% 6.57/2.29  tff(c_1594, plain, (![C_384, B_385, A_386]: (r2_hidden(C_384, B_385) | ~r2_hidden(k3_subset_1(A_386, C_384), k7_setfam_1(A_386, B_385)) | ~m1_subset_1(C_384, k1_zfmisc_1(A_386)) | ~m1_subset_1(B_385, k1_zfmisc_1(k1_zfmisc_1(A_386))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.57/2.29  tff(c_1609, plain, (![C_384]: (r2_hidden(C_384, k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(k3_subset_1('#skF_3', C_384), '#skF_4') | ~m1_subset_1(C_384, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_820, c_1594])).
% 6.57/2.29  tff(c_2186, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1609])).
% 6.57/2.29  tff(c_2189, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_112, c_2186])).
% 6.57/2.29  tff(c_2196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_2189])).
% 6.57/2.29  tff(c_2198, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1609])).
% 6.57/2.29  tff(c_1720, plain, (![B_413, C_414, A_415]: (r1_tarski(B_413, C_414) | ~r1_tarski(k7_setfam_1(A_415, B_413), k7_setfam_1(A_415, C_414)) | ~m1_subset_1(C_414, k1_zfmisc_1(k1_zfmisc_1(A_415))) | ~m1_subset_1(B_413, k1_zfmisc_1(k1_zfmisc_1(A_415))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.57/2.29  tff(c_1741, plain, (![C_414]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), C_414) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', C_414)) | ~m1_subset_1(C_414, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_820, c_1720])).
% 6.57/2.29  tff(c_2422, plain, (![C_656]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), C_656) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', C_656)) | ~m1_subset_1(C_656, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_1741])).
% 6.57/2.29  tff(c_3671, plain, (![A_861]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), k1_tarski(A_861)) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_861))) | ~r2_hidden(A_861, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_110, c_2422])).
% 6.57/2.29  tff(c_26, plain, (![B_37, A_36]: (k1_tarski(B_37)=A_36 | k1_xboole_0=A_36 | ~r1_tarski(A_36, k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.57/2.29  tff(c_3674, plain, (![A_861]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_861) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_861))) | ~r2_hidden(A_861, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_3671, c_26])).
% 6.57/2.29  tff(c_3684, plain, (![A_871]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_871) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_871))) | ~r2_hidden(A_871, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_693, c_3674])).
% 6.57/2.29  tff(c_3697, plain, (![A_872]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_872) | ~r2_hidden(k1_xboole_0, k1_tarski(A_872)) | ~r2_hidden(A_872, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_3086, c_3684])).
% 6.57/2.29  tff(c_3703, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(k1_xboole_0) | ~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_249, c_3697])).
% 6.57/2.29  tff(c_3709, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_126, c_3703])).
% 6.57/2.29  tff(c_3713, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3')) | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_3709])).
% 6.57/2.29  tff(c_3716, plain, (v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_3713])).
% 6.57/2.29  tff(c_3718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_3716])).
% 6.57/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.29  
% 6.57/2.29  Inference rules
% 6.57/2.29  ----------------------
% 6.57/2.29  #Ref     : 0
% 6.57/2.29  #Sup     : 768
% 6.57/2.29  #Fact    : 0
% 6.57/2.29  #Define  : 0
% 6.57/2.29  #Split   : 12
% 6.57/2.29  #Chain   : 0
% 6.57/2.29  #Close   : 0
% 6.57/2.29  
% 6.57/2.29  Ordering : KBO
% 6.57/2.29  
% 6.57/2.29  Simplification rules
% 6.57/2.29  ----------------------
% 6.57/2.29  #Subsume      : 211
% 6.57/2.29  #Demod        : 298
% 6.57/2.29  #Tautology    : 251
% 6.57/2.29  #SimpNegUnit  : 66
% 6.57/2.29  #BackRed      : 10
% 6.57/2.29  
% 6.57/2.29  #Partial instantiations: 0
% 6.57/2.29  #Strategies tried      : 1
% 6.57/2.29  
% 6.57/2.29  Timing (in seconds)
% 6.57/2.29  ----------------------
% 6.57/2.30  Preprocessing        : 0.40
% 6.57/2.30  Parsing              : 0.20
% 6.57/2.30  CNF conversion       : 0.03
% 6.57/2.30  Main loop            : 1.14
% 6.57/2.30  Inferencing          : 0.39
% 6.57/2.30  Reduction            : 0.38
% 6.57/2.30  Demodulation         : 0.28
% 6.57/2.30  BG Simplification    : 0.04
% 6.57/2.30  Subsumption          : 0.26
% 6.57/2.30  Abstraction          : 0.04
% 6.57/2.30  MUC search           : 0.00
% 6.57/2.30  Cooper               : 0.00
% 6.57/2.30  Total                : 1.57
% 6.57/2.30  Index Insertion      : 0.00
% 6.57/2.30  Index Deletion       : 0.00
% 6.57/2.30  Index Matching       : 0.00
% 6.57/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
