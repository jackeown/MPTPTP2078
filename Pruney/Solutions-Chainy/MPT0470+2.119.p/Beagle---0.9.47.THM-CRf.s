%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 215 expanded)
%              Number of leaves         :   48 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 348 expanded)
%              Number of equality atoms :   66 ( 142 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_118,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_16,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1547,plain,(
    ! [A_264,B_265] : k5_xboole_0(A_264,k3_xboole_0(A_264,B_265)) = k4_xboole_0(A_264,B_265) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1559,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1547])).

tff(c_1562,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1559])).

tff(c_822,plain,(
    ! [A_175,B_176] : k5_xboole_0(A_175,k3_xboole_0(A_175,B_176)) = k4_xboole_0(A_175,B_176) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_834,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_822])).

tff(c_837,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_834])).

tff(c_64,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_115,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_1'(A_48),A_48)
      | v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_179,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k1_tarski(A_92),B_93)
      | ~ r2_hidden(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [A_95] :
      ( k1_tarski(A_95) = k1_xboole_0
      | ~ r2_hidden(A_95,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_179,c_14])).

tff(c_214,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_209])).

tff(c_215,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( v1_relat_1(k5_relat_1(A_66,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_132,plain,(
    ! [A_82,B_83] :
      ( v1_xboole_0(k2_zfmisc_1(A_82,B_83))
      | ~ v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ! [A_87,B_88] :
      ( k2_zfmisc_1(A_87,B_88) = k1_xboole_0
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_152,plain,(
    ! [B_88] : k2_zfmisc_1(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_143])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_691,plain,(
    ! [A_156,B_157] :
      ( k1_relat_1(k5_relat_1(A_156,B_157)) = k1_relat_1(A_156)
      | ~ r1_tarski(k2_relat_1(A_156),k1_relat_1(B_157))
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_697,plain,(
    ! [B_157] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_157)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_157))
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_691])).

tff(c_702,plain,(
    ! [B_158] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_158)) = k1_xboole_0
      | ~ v1_relat_1(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_12,c_62,c_697])).

tff(c_54,plain,(
    ! [A_68] :
      ( k3_xboole_0(A_68,k2_zfmisc_1(k1_relat_1(A_68),k2_relat_1(A_68))) = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_714,plain,(
    ! [B_158] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_158),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_158)))) = k5_relat_1(k1_xboole_0,B_158)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_158))
      | ~ v1_relat_1(B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_54])).

tff(c_722,plain,(
    ! [B_159] :
      ( k5_relat_1(k1_xboole_0,B_159) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_159))
      | ~ v1_relat_1(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_152,c_714])).

tff(c_726,plain,(
    ! [B_67] :
      ( k5_relat_1(k1_xboole_0,B_67) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_722])).

tff(c_730,plain,(
    ! [B_160] :
      ( k5_relat_1(k1_xboole_0,B_160) = k1_xboole_0
      | ~ v1_relat_1(B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_726])).

tff(c_739,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_730])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_739])).

tff(c_746,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_765,plain,(
    ! [B_163] : k4_xboole_0(k1_tarski(B_163),k1_tarski(B_163)) != k1_tarski(B_163) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_768,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_765])).

tff(c_772,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_746,c_768])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_772])).

tff(c_842,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_944,plain,(
    ! [A_192,B_193] :
      ( r1_tarski(k1_tarski(A_192),B_193)
      | ~ r2_hidden(A_192,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_950,plain,(
    ! [A_194] :
      ( k1_tarski(A_194) = k1_xboole_0
      | ~ r2_hidden(A_194,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_944,c_14])).

tff(c_955,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_950])).

tff(c_956,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_864,plain,(
    ! [A_179,B_180] :
      ( v1_xboole_0(k2_zfmisc_1(A_179,B_180))
      | ~ v1_xboole_0(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_875,plain,(
    ! [A_184,B_185] :
      ( k2_zfmisc_1(A_184,B_185) = k1_xboole_0
      | ~ v1_xboole_0(B_185) ) ),
    inference(resolution,[status(thm)],[c_864,c_6])).

tff(c_884,plain,(
    ! [A_184] : k2_zfmisc_1(A_184,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_875])).

tff(c_1419,plain,(
    ! [B_247,A_248] :
      ( k2_relat_1(k5_relat_1(B_247,A_248)) = k2_relat_1(A_248)
      | ~ r1_tarski(k1_relat_1(A_248),k2_relat_1(B_247))
      | ~ v1_relat_1(B_247)
      | ~ v1_relat_1(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1422,plain,(
    ! [B_247] :
      ( k2_relat_1(k5_relat_1(B_247,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_247))
      | ~ v1_relat_1(B_247)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1419])).

tff(c_1430,plain,(
    ! [B_249] :
      ( k2_relat_1(k5_relat_1(B_249,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_12,c_60,c_1422])).

tff(c_1442,plain,(
    ! [B_249] :
      ( k3_xboole_0(k5_relat_1(B_249,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_249,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_249,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_249,k1_xboole_0))
      | ~ v1_relat_1(B_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_54])).

tff(c_1450,plain,(
    ! [B_250] :
      ( k5_relat_1(B_250,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_250,k1_xboole_0))
      | ~ v1_relat_1(B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_884,c_1442])).

tff(c_1454,plain,(
    ! [A_66] :
      ( k5_relat_1(A_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_52,c_1450])).

tff(c_1458,plain,(
    ! [A_251] :
      ( k5_relat_1(A_251,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_1454])).

tff(c_1467,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_1458])).

tff(c_1473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_1467])).

tff(c_1474,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1531,plain,(
    ! [B_261] : k4_xboole_0(k1_tarski(B_261),k1_tarski(B_261)) != k1_tarski(B_261) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1534,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_1531])).

tff(c_1538,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_1474,c_1534])).

tff(c_1566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.54  
% 3.24/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.54  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.24/1.54  
% 3.24/1.54  %Foreground sorts:
% 3.24/1.54  
% 3.24/1.54  
% 3.24/1.54  %Background operators:
% 3.24/1.54  
% 3.24/1.54  
% 3.24/1.54  %Foreground operators:
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.24/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.24/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.24/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.24/1.54  
% 3.24/1.55  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.24/1.55  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.24/1.55  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.24/1.55  tff(f_125, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.24/1.55  tff(f_87, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.24/1.55  tff(f_70, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.24/1.55  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.24/1.55  tff(f_93, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.24/1.55  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.24/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.55  tff(f_66, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.24/1.55  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.24/1.55  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.24/1.55  tff(f_118, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.24/1.55  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.24/1.55  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.24/1.55  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.24/1.55  tff(f_62, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.24/1.55  tff(f_115, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.24/1.55  tff(c_16, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.55  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.24/1.55  tff(c_1547, plain, (![A_264, B_265]: (k5_xboole_0(A_264, k3_xboole_0(A_264, B_265))=k4_xboole_0(A_264, B_265))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.55  tff(c_1559, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1547])).
% 3.24/1.55  tff(c_1562, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1559])).
% 3.24/1.55  tff(c_822, plain, (![A_175, B_176]: (k5_xboole_0(A_175, k3_xboole_0(A_175, B_176))=k4_xboole_0(A_175, B_176))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.55  tff(c_834, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_822])).
% 3.24/1.55  tff(c_837, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_834])).
% 3.24/1.55  tff(c_64, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.24/1.55  tff(c_115, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 3.24/1.55  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.24/1.55  tff(c_50, plain, (![A_48]: (r2_hidden('#skF_1'(A_48), A_48) | v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.24/1.55  tff(c_179, plain, (![A_92, B_93]: (r1_tarski(k1_tarski(A_92), B_93) | ~r2_hidden(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.55  tff(c_14, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.55  tff(c_209, plain, (![A_95]: (k1_tarski(A_95)=k1_xboole_0 | ~r2_hidden(A_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_179, c_14])).
% 3.24/1.55  tff(c_214, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_209])).
% 3.24/1.55  tff(c_215, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_214])).
% 3.24/1.55  tff(c_52, plain, (![A_66, B_67]: (v1_relat_1(k5_relat_1(A_66, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.55  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.24/1.55  tff(c_132, plain, (![A_82, B_83]: (v1_xboole_0(k2_zfmisc_1(A_82, B_83)) | ~v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.55  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.55  tff(c_143, plain, (![A_87, B_88]: (k2_zfmisc_1(A_87, B_88)=k1_xboole_0 | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_132, c_6])).
% 3.24/1.55  tff(c_152, plain, (![B_88]: (k2_zfmisc_1(k1_xboole_0, B_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_143])).
% 3.24/1.55  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.55  tff(c_62, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.24/1.55  tff(c_60, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.24/1.55  tff(c_691, plain, (![A_156, B_157]: (k1_relat_1(k5_relat_1(A_156, B_157))=k1_relat_1(A_156) | ~r1_tarski(k2_relat_1(A_156), k1_relat_1(B_157)) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.24/1.55  tff(c_697, plain, (![B_157]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_157))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_157)) | ~v1_relat_1(B_157) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_691])).
% 3.24/1.55  tff(c_702, plain, (![B_158]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_158))=k1_xboole_0 | ~v1_relat_1(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_12, c_62, c_697])).
% 3.24/1.55  tff(c_54, plain, (![A_68]: (k3_xboole_0(A_68, k2_zfmisc_1(k1_relat_1(A_68), k2_relat_1(A_68)))=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.24/1.55  tff(c_714, plain, (![B_158]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_158), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_158))))=k5_relat_1(k1_xboole_0, B_158) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_158)) | ~v1_relat_1(B_158))), inference(superposition, [status(thm), theory('equality')], [c_702, c_54])).
% 3.24/1.55  tff(c_722, plain, (![B_159]: (k5_relat_1(k1_xboole_0, B_159)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_159)) | ~v1_relat_1(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_152, c_714])).
% 3.24/1.55  tff(c_726, plain, (![B_67]: (k5_relat_1(k1_xboole_0, B_67)=k1_xboole_0 | ~v1_relat_1(B_67) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_722])).
% 3.24/1.55  tff(c_730, plain, (![B_160]: (k5_relat_1(k1_xboole_0, B_160)=k1_xboole_0 | ~v1_relat_1(B_160))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_726])).
% 3.24/1.55  tff(c_739, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_730])).
% 3.24/1.55  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_739])).
% 3.24/1.55  tff(c_746, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_214])).
% 3.24/1.55  tff(c_765, plain, (![B_163]: (k4_xboole_0(k1_tarski(B_163), k1_tarski(B_163))!=k1_tarski(B_163))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.55  tff(c_768, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_746, c_765])).
% 3.24/1.55  tff(c_772, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_746, c_746, c_768])).
% 3.24/1.55  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_837, c_772])).
% 3.24/1.55  tff(c_842, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 3.24/1.55  tff(c_944, plain, (![A_192, B_193]: (r1_tarski(k1_tarski(A_192), B_193) | ~r2_hidden(A_192, B_193))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.55  tff(c_950, plain, (![A_194]: (k1_tarski(A_194)=k1_xboole_0 | ~r2_hidden(A_194, k1_xboole_0))), inference(resolution, [status(thm)], [c_944, c_14])).
% 3.24/1.55  tff(c_955, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_950])).
% 3.24/1.55  tff(c_956, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_955])).
% 3.24/1.55  tff(c_864, plain, (![A_179, B_180]: (v1_xboole_0(k2_zfmisc_1(A_179, B_180)) | ~v1_xboole_0(B_180))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.55  tff(c_875, plain, (![A_184, B_185]: (k2_zfmisc_1(A_184, B_185)=k1_xboole_0 | ~v1_xboole_0(B_185))), inference(resolution, [status(thm)], [c_864, c_6])).
% 3.24/1.55  tff(c_884, plain, (![A_184]: (k2_zfmisc_1(A_184, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_875])).
% 3.24/1.55  tff(c_1419, plain, (![B_247, A_248]: (k2_relat_1(k5_relat_1(B_247, A_248))=k2_relat_1(A_248) | ~r1_tarski(k1_relat_1(A_248), k2_relat_1(B_247)) | ~v1_relat_1(B_247) | ~v1_relat_1(A_248))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.24/1.55  tff(c_1422, plain, (![B_247]: (k2_relat_1(k5_relat_1(B_247, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_247)) | ~v1_relat_1(B_247) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1419])).
% 3.24/1.55  tff(c_1430, plain, (![B_249]: (k2_relat_1(k5_relat_1(B_249, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_249))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_12, c_60, c_1422])).
% 3.24/1.55  tff(c_1442, plain, (![B_249]: (k3_xboole_0(k5_relat_1(B_249, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_249, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_249, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_249, k1_xboole_0)) | ~v1_relat_1(B_249))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_54])).
% 3.24/1.55  tff(c_1450, plain, (![B_250]: (k5_relat_1(B_250, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_250, k1_xboole_0)) | ~v1_relat_1(B_250))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_884, c_1442])).
% 3.24/1.55  tff(c_1454, plain, (![A_66]: (k5_relat_1(A_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_52, c_1450])).
% 3.24/1.55  tff(c_1458, plain, (![A_251]: (k5_relat_1(A_251, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_1454])).
% 3.24/1.55  tff(c_1467, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_1458])).
% 3.24/1.56  tff(c_1473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_842, c_1467])).
% 3.24/1.56  tff(c_1474, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_955])).
% 3.24/1.56  tff(c_1531, plain, (![B_261]: (k4_xboole_0(k1_tarski(B_261), k1_tarski(B_261))!=k1_tarski(B_261))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.56  tff(c_1534, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1474, c_1531])).
% 3.24/1.56  tff(c_1538, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_1474, c_1534])).
% 3.24/1.56  tff(c_1566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1562, c_1538])).
% 3.24/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.56  
% 3.24/1.56  Inference rules
% 3.24/1.56  ----------------------
% 3.24/1.56  #Ref     : 2
% 3.24/1.56  #Sup     : 341
% 3.24/1.56  #Fact    : 0
% 3.24/1.56  #Define  : 0
% 3.24/1.56  #Split   : 3
% 3.24/1.56  #Chain   : 0
% 3.24/1.56  #Close   : 0
% 3.24/1.56  
% 3.24/1.56  Ordering : KBO
% 3.24/1.56  
% 3.24/1.56  Simplification rules
% 3.24/1.56  ----------------------
% 3.24/1.56  #Subsume      : 5
% 3.24/1.56  #Demod        : 180
% 3.24/1.56  #Tautology    : 278
% 3.24/1.56  #SimpNegUnit  : 9
% 3.24/1.56  #BackRed      : 8
% 3.24/1.56  
% 3.24/1.56  #Partial instantiations: 0
% 3.24/1.56  #Strategies tried      : 1
% 3.24/1.56  
% 3.24/1.56  Timing (in seconds)
% 3.24/1.56  ----------------------
% 3.24/1.56  Preprocessing        : 0.32
% 3.24/1.56  Parsing              : 0.17
% 3.24/1.56  CNF conversion       : 0.02
% 3.24/1.56  Main loop            : 0.40
% 3.24/1.56  Inferencing          : 0.15
% 3.24/1.56  Reduction            : 0.12
% 3.24/1.56  Demodulation         : 0.08
% 3.24/1.56  BG Simplification    : 0.02
% 3.24/1.56  Subsumption          : 0.07
% 3.24/1.56  Abstraction          : 0.02
% 3.24/1.56  MUC search           : 0.00
% 3.24/1.56  Cooper               : 0.00
% 3.24/1.56  Total                : 0.76
% 3.24/1.56  Index Insertion      : 0.00
% 3.24/1.56  Index Deletion       : 0.00
% 3.24/1.56  Index Matching       : 0.00
% 3.24/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
