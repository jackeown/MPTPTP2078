%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 148 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 283 expanded)
%              Number of equality atoms :   32 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_47,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_96,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_70,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_56,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_112,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden('#skF_2'(A_16,B_17,C_18),B_17)
      | ~ r2_hidden(A_16,k9_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_916,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_2'(A_129,B_130,C_131),k1_relat_1(C_131))
      | ~ r2_hidden(A_129,k9_relat_1(C_131,B_130))
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_133,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_62])).

tff(c_434,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_446,plain,(
    ! [C_85] :
      ( ~ r2_hidden(C_85,'#skF_3')
      | ~ r2_hidden(C_85,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_133,c_434])).

tff(c_933,plain,(
    ! [A_129,B_130] :
      ( ~ r2_hidden('#skF_2'(A_129,B_130,'#skF_4'),'#skF_3')
      | ~ r2_hidden(A_129,k9_relat_1('#skF_4',B_130))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_916,c_446])).

tff(c_1337,plain,(
    ! [A_177,B_178] :
      ( ~ r2_hidden('#skF_2'(A_177,B_178,'#skF_4'),'#skF_3')
      | ~ r2_hidden(A_177,k9_relat_1('#skF_4',B_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_933])).

tff(c_1341,plain,(
    ! [A_16] :
      ( ~ r2_hidden(A_16,k9_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_1337])).

tff(c_1345,plain,(
    ! [A_179] : ~ r2_hidden(A_179,k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1341])).

tff(c_1371,plain,(
    ! [B_180] : r1_xboole_0(k9_relat_1('#skF_4','#skF_3'),B_180) ),
    inference(resolution,[status(thm)],[c_8,c_1345])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ r1_xboole_0(A_8,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1379,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1371,c_12])).

tff(c_1385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1379])).

tff(c_1386,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1392,plain,(
    ! [A_181,B_182] : ~ r2_hidden(A_181,k2_zfmisc_1(A_181,B_182)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1398,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1392])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1387,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1476,plain,(
    ! [A_202] :
      ( r1_tarski(A_202,k2_zfmisc_1(k1_relat_1(A_202),k2_relat_1(A_202)))
      | ~ v1_relat_1(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4478,plain,(
    ! [B_407,A_408] :
      ( r1_tarski(k7_relat_1(B_407,A_408),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_407,A_408)),k9_relat_1(B_407,A_408)))
      | ~ v1_relat_1(k7_relat_1(B_407,A_408))
      | ~ v1_relat_1(B_407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1476])).

tff(c_4528,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_4478])).

tff(c_4554,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16,c_4528])).

tff(c_4555,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4554])).

tff(c_4558,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4555])).

tff(c_4562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4558])).

tff(c_4563,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4554])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1498,plain,(
    ! [B_203,A_204] :
      ( k7_relat_1(B_203,A_204) = B_203
      | ~ r1_tarski(k1_relat_1(B_203),A_204)
      | ~ v1_relat_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1505,plain,(
    ! [A_25,A_204] :
      ( k7_relat_1(k6_relat_1(A_25),A_204) = k6_relat_1(A_25)
      | ~ r1_tarski(A_25,A_204)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1498])).

tff(c_1719,plain,(
    ! [A_235,A_236] :
      ( k7_relat_1(k6_relat_1(A_235),A_236) = k6_relat_1(A_235)
      | ~ r1_tarski(A_235,A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1505])).

tff(c_1731,plain,(
    ! [A_235,A_236] :
      ( k9_relat_1(k6_relat_1(A_235),A_236) = k2_relat_1(k6_relat_1(A_235))
      | ~ v1_relat_1(k6_relat_1(A_235))
      | ~ r1_tarski(A_235,A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1719,c_34])).

tff(c_1999,plain,(
    ! [A_262,A_263] :
      ( k9_relat_1(k6_relat_1(A_262),A_263) = A_262
      | ~ r1_tarski(A_262,A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_44,c_1731])).

tff(c_1748,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden('#skF_2'(A_237,B_238,C_239),B_238)
      | ~ r2_hidden(A_237,k9_relat_1(C_239,B_238))
      | ~ v1_relat_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1764,plain,(
    ! [A_240,C_241] :
      ( ~ r2_hidden(A_240,k9_relat_1(C_241,k1_xboole_0))
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_1748,c_1398])).

tff(c_1780,plain,(
    ! [C_242,A_243] :
      ( ~ v1_relat_1(C_242)
      | r1_xboole_0(A_243,k9_relat_1(C_242,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1764])).

tff(c_1792,plain,(
    ! [C_244] :
      ( k9_relat_1(C_244,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_244) ) ),
    inference(resolution,[status(thm)],[c_1780,c_12])).

tff(c_1807,plain,(
    ! [A_13] : k9_relat_1(k6_relat_1(A_13),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1792])).

tff(c_2010,plain,(
    ! [A_262] :
      ( k1_xboole_0 = A_262
      | ~ r1_tarski(A_262,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1999,c_1807])).

tff(c_4608,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4563,c_2010])).

tff(c_46,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(k7_relat_1(C_28,B_27)))
      | ~ r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(A_26,B_27)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4637,plain,(
    ! [A_26] :
      ( r2_hidden(A_26,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_26,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_26,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4608,c_46])).

tff(c_4667,plain,(
    ! [A_26] :
      ( r2_hidden(A_26,k1_xboole_0)
      | ~ r2_hidden(A_26,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_26,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_4637])).

tff(c_4887,plain,(
    ! [A_413] :
      ( ~ r2_hidden(A_413,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_413,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1398,c_4667])).

tff(c_5058,plain,(
    ! [A_418] :
      ( ~ r2_hidden('#skF_1'(A_418,k1_relat_1('#skF_4')),'#skF_3')
      | r1_xboole_0(A_418,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_4887])).

tff(c_5078,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_5058])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5082,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5078,c_2])).

tff(c_5087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1386,c_5082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.97  
% 5.07/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.07/1.97  
% 5.07/1.97  %Foreground sorts:
% 5.07/1.97  
% 5.07/1.97  
% 5.07/1.97  %Background operators:
% 5.07/1.97  
% 5.07/1.97  
% 5.07/1.97  %Foreground operators:
% 5.07/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/1.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.07/1.97  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.07/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.07/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.07/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.07/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.07/1.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.07/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.07/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.07/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.07/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.07/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.07/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.07/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.07/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.07/1.97  
% 5.26/1.99  tff(f_121, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 5.26/1.99  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.26/1.99  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.26/1.99  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.26/1.99  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.26/1.99  tff(f_68, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.26/1.99  tff(f_96, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.26/1.99  tff(f_74, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.26/1.99  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.26/1.99  tff(f_93, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 5.26/1.99  tff(f_70, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.26/1.99  tff(f_100, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.26/1.99  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.26/1.99  tff(f_108, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 5.26/1.99  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.26/1.99  tff(c_56, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.26/1.99  tff(c_112, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 5.26/1.99  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.26/1.99  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.26/1.99  tff(c_28, plain, (![A_16, B_17, C_18]: (r2_hidden('#skF_2'(A_16, B_17, C_18), B_17) | ~r2_hidden(A_16, k9_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.26/1.99  tff(c_916, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_2'(A_129, B_130, C_131), k1_relat_1(C_131)) | ~r2_hidden(A_129, k9_relat_1(C_131, B_130)) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.26/1.99  tff(c_62, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.26/1.99  tff(c_133, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_112, c_62])).
% 5.26/1.99  tff(c_434, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.26/1.99  tff(c_446, plain, (![C_85]: (~r2_hidden(C_85, '#skF_3') | ~r2_hidden(C_85, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_133, c_434])).
% 5.26/1.99  tff(c_933, plain, (![A_129, B_130]: (~r2_hidden('#skF_2'(A_129, B_130, '#skF_4'), '#skF_3') | ~r2_hidden(A_129, k9_relat_1('#skF_4', B_130)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_916, c_446])).
% 5.26/1.99  tff(c_1337, plain, (![A_177, B_178]: (~r2_hidden('#skF_2'(A_177, B_178, '#skF_4'), '#skF_3') | ~r2_hidden(A_177, k9_relat_1('#skF_4', B_178)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_933])).
% 5.26/1.99  tff(c_1341, plain, (![A_16]: (~r2_hidden(A_16, k9_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_1337])).
% 5.26/1.99  tff(c_1345, plain, (![A_179]: (~r2_hidden(A_179, k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1341])).
% 5.26/1.99  tff(c_1371, plain, (![B_180]: (r1_xboole_0(k9_relat_1('#skF_4', '#skF_3'), B_180))), inference(resolution, [status(thm)], [c_8, c_1345])).
% 5.26/1.99  tff(c_12, plain, (![A_8]: (~r1_xboole_0(A_8, A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.26/1.99  tff(c_1379, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1371, c_12])).
% 5.26/1.99  tff(c_1385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_1379])).
% 5.26/1.99  tff(c_1386, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 5.26/1.99  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.26/1.99  tff(c_16, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.26/1.99  tff(c_1392, plain, (![A_181, B_182]: (~r2_hidden(A_181, k2_zfmisc_1(A_181, B_182)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.26/1.99  tff(c_1398, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1392])).
% 5.26/1.99  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/1.99  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/1.99  tff(c_1387, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 5.26/1.99  tff(c_34, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.26/1.99  tff(c_1476, plain, (![A_202]: (r1_tarski(A_202, k2_zfmisc_1(k1_relat_1(A_202), k2_relat_1(A_202))) | ~v1_relat_1(A_202))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.26/1.99  tff(c_4478, plain, (![B_407, A_408]: (r1_tarski(k7_relat_1(B_407, A_408), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_407, A_408)), k9_relat_1(B_407, A_408))) | ~v1_relat_1(k7_relat_1(B_407, A_408)) | ~v1_relat_1(B_407))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1476])).
% 5.26/1.99  tff(c_4528, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_xboole_0)) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1387, c_4478])).
% 5.26/1.99  tff(c_4554, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16, c_4528])).
% 5.26/1.99  tff(c_4555, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4554])).
% 5.26/1.99  tff(c_4558, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4555])).
% 5.26/1.99  tff(c_4562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_4558])).
% 5.26/1.99  tff(c_4563, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_4554])).
% 5.26/1.99  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.26/1.99  tff(c_44, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.26/1.99  tff(c_42, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.26/1.99  tff(c_1498, plain, (![B_203, A_204]: (k7_relat_1(B_203, A_204)=B_203 | ~r1_tarski(k1_relat_1(B_203), A_204) | ~v1_relat_1(B_203))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.26/1.99  tff(c_1505, plain, (![A_25, A_204]: (k7_relat_1(k6_relat_1(A_25), A_204)=k6_relat_1(A_25) | ~r1_tarski(A_25, A_204) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1498])).
% 5.26/1.99  tff(c_1719, plain, (![A_235, A_236]: (k7_relat_1(k6_relat_1(A_235), A_236)=k6_relat_1(A_235) | ~r1_tarski(A_235, A_236))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1505])).
% 5.26/1.99  tff(c_1731, plain, (![A_235, A_236]: (k9_relat_1(k6_relat_1(A_235), A_236)=k2_relat_1(k6_relat_1(A_235)) | ~v1_relat_1(k6_relat_1(A_235)) | ~r1_tarski(A_235, A_236))), inference(superposition, [status(thm), theory('equality')], [c_1719, c_34])).
% 5.26/1.99  tff(c_1999, plain, (![A_262, A_263]: (k9_relat_1(k6_relat_1(A_262), A_263)=A_262 | ~r1_tarski(A_262, A_263))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_44, c_1731])).
% 5.26/1.99  tff(c_1748, plain, (![A_237, B_238, C_239]: (r2_hidden('#skF_2'(A_237, B_238, C_239), B_238) | ~r2_hidden(A_237, k9_relat_1(C_239, B_238)) | ~v1_relat_1(C_239))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.26/1.99  tff(c_1764, plain, (![A_240, C_241]: (~r2_hidden(A_240, k9_relat_1(C_241, k1_xboole_0)) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_1748, c_1398])).
% 5.26/1.99  tff(c_1780, plain, (![C_242, A_243]: (~v1_relat_1(C_242) | r1_xboole_0(A_243, k9_relat_1(C_242, k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_1764])).
% 5.26/1.99  tff(c_1792, plain, (![C_244]: (k9_relat_1(C_244, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_244))), inference(resolution, [status(thm)], [c_1780, c_12])).
% 5.26/1.99  tff(c_1807, plain, (![A_13]: (k9_relat_1(k6_relat_1(A_13), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1792])).
% 5.26/1.99  tff(c_2010, plain, (![A_262]: (k1_xboole_0=A_262 | ~r1_tarski(A_262, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1999, c_1807])).
% 5.26/1.99  tff(c_4608, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4563, c_2010])).
% 5.26/1.99  tff(c_46, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(k7_relat_1(C_28, B_27))) | ~r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(A_26, B_27) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.26/1.99  tff(c_4637, plain, (![A_26]: (r2_hidden(A_26, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_26, k1_relat_1('#skF_4')) | ~r2_hidden(A_26, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4608, c_46])).
% 5.26/1.99  tff(c_4667, plain, (![A_26]: (r2_hidden(A_26, k1_xboole_0) | ~r2_hidden(A_26, k1_relat_1('#skF_4')) | ~r2_hidden(A_26, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_4637])).
% 5.26/1.99  tff(c_4887, plain, (![A_413]: (~r2_hidden(A_413, k1_relat_1('#skF_4')) | ~r2_hidden(A_413, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1398, c_4667])).
% 5.26/1.99  tff(c_5058, plain, (![A_418]: (~r2_hidden('#skF_1'(A_418, k1_relat_1('#skF_4')), '#skF_3') | r1_xboole_0(A_418, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_4887])).
% 5.26/1.99  tff(c_5078, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_5058])).
% 5.26/1.99  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.26/1.99  tff(c_5082, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_5078, c_2])).
% 5.26/1.99  tff(c_5087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1386, c_5082])).
% 5.26/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.99  
% 5.26/1.99  Inference rules
% 5.26/1.99  ----------------------
% 5.26/1.99  #Ref     : 0
% 5.26/1.99  #Sup     : 1075
% 5.26/1.99  #Fact    : 0
% 5.26/1.99  #Define  : 0
% 5.26/1.99  #Split   : 8
% 5.26/1.99  #Chain   : 0
% 5.26/1.99  #Close   : 0
% 5.26/1.99  
% 5.26/1.99  Ordering : KBO
% 5.26/1.99  
% 5.26/1.99  Simplification rules
% 5.26/1.99  ----------------------
% 5.26/1.99  #Subsume      : 267
% 5.26/1.99  #Demod        : 974
% 5.26/1.99  #Tautology    : 377
% 5.26/1.99  #SimpNegUnit  : 44
% 5.26/1.99  #BackRed      : 15
% 5.26/1.99  
% 5.26/1.99  #Partial instantiations: 0
% 5.26/1.99  #Strategies tried      : 1
% 5.26/1.99  
% 5.26/1.99  Timing (in seconds)
% 5.26/1.99  ----------------------
% 5.26/1.99  Preprocessing        : 0.31
% 5.26/1.99  Parsing              : 0.17
% 5.26/1.99  CNF conversion       : 0.02
% 5.26/1.99  Main loop            : 0.86
% 5.26/1.99  Inferencing          : 0.32
% 5.26/1.99  Reduction            : 0.27
% 5.26/1.99  Demodulation         : 0.19
% 5.26/1.99  BG Simplification    : 0.03
% 5.26/1.99  Subsumption          : 0.17
% 5.26/1.99  Abstraction          : 0.04
% 5.26/1.99  MUC search           : 0.00
% 5.26/1.99  Cooper               : 0.00
% 5.26/1.99  Total                : 1.20
% 5.26/1.99  Index Insertion      : 0.00
% 5.26/1.99  Index Deletion       : 0.00
% 5.26/1.99  Index Matching       : 0.00
% 5.26/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
