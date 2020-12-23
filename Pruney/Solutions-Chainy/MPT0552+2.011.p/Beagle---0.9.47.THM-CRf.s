%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 27.19s
% Output     : CNFRefutation 27.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 189 expanded)
%              Number of leaves         :   29 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 385 expanded)
%              Number of equality atoms :    9 (  34 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k7_relat_1(A_22,B_23))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30895,plain,(
    ! [C_549,A_550,B_551] :
      ( k3_xboole_0(k7_relat_1(C_549,A_550),k7_relat_1(C_549,B_551)) = k7_relat_1(C_549,k3_xboole_0(A_550,B_551))
      | ~ v1_relat_1(C_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6])).

tff(c_117,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_30918,plain,(
    ! [C_549,A_550,B_551] :
      ( r1_tarski(k7_relat_1(C_549,k3_xboole_0(A_550,B_551)),k7_relat_1(C_549,B_551))
      | ~ v1_relat_1(C_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30895,c_117])).

tff(c_28,plain,(
    ! [B_31,A_30] :
      ( k2_relat_1(k7_relat_1(B_31,A_30)) = k9_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30830,plain,(
    ! [A_542,B_543] :
      ( r1_tarski(k2_relat_1(A_542),k2_relat_1(B_543))
      | ~ r1_tarski(A_542,B_543)
      | ~ v1_relat_1(B_543)
      | ~ v1_relat_1(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32585,plain,(
    ! [B_628,A_629,B_630] :
      ( r1_tarski(k9_relat_1(B_628,A_629),k2_relat_1(B_630))
      | ~ r1_tarski(k7_relat_1(B_628,A_629),B_630)
      | ~ v1_relat_1(B_630)
      | ~ v1_relat_1(k7_relat_1(B_628,A_629))
      | ~ v1_relat_1(B_628) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_30830])).

tff(c_58590,plain,(
    ! [B_970,A_971,B_972,A_973] :
      ( r1_tarski(k9_relat_1(B_970,A_971),k9_relat_1(B_972,A_973))
      | ~ r1_tarski(k7_relat_1(B_970,A_971),k7_relat_1(B_972,A_973))
      | ~ v1_relat_1(k7_relat_1(B_972,A_973))
      | ~ v1_relat_1(k7_relat_1(B_970,A_971))
      | ~ v1_relat_1(B_970)
      | ~ v1_relat_1(B_972) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_32585])).

tff(c_417,plain,(
    ! [C_91,A_92,B_93] :
      ( k3_xboole_0(k7_relat_1(C_91,A_92),k7_relat_1(C_91,B_93)) = k7_relat_1(C_91,k3_xboole_0(A_92,B_93))
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [A_49,B_50] : r1_tarski(k3_xboole_0(A_49,B_50),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6])).

tff(c_443,plain,(
    ! [C_91,A_92,B_93] :
      ( r1_tarski(k7_relat_1(C_91,k3_xboole_0(A_92,B_93)),k7_relat_1(C_91,A_92))
      | ~ v1_relat_1(C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_105])).

tff(c_291,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k2_relat_1(A_82),k2_relat_1(B_83))
      | ~ r1_tarski(A_82,B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2233,plain,(
    ! [B_172,A_173,B_174] :
      ( r1_tarski(k9_relat_1(B_172,A_173),k2_relat_1(B_174))
      | ~ r1_tarski(k7_relat_1(B_172,A_173),B_174)
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(k7_relat_1(B_172,A_173))
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_291])).

tff(c_30761,plain,(
    ! [B_538,A_539,B_540,A_541] :
      ( r1_tarski(k9_relat_1(B_538,A_539),k9_relat_1(B_540,A_541))
      | ~ r1_tarski(k7_relat_1(B_538,A_539),k7_relat_1(B_540,A_541))
      | ~ v1_relat_1(k7_relat_1(B_540,A_541))
      | ~ v1_relat_1(k7_relat_1(B_538,A_539))
      | ~ v1_relat_1(B_538)
      | ~ v1_relat_1(B_540) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2233])).

tff(c_248,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(A_74,k3_xboole_0(B_75,C_76))
      | ~ r1_tarski(A_74,C_76)
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_262,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_248,c_34])).

tff(c_290,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_30764,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30761,c_290])).

tff(c_30794,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30764])).

tff(c_30796,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_30794])).

tff(c_30799,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_30796])).

tff(c_30803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30799])).

tff(c_30804,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_30794])).

tff(c_30806,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_30804])).

tff(c_30809,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_443,c_30806])).

tff(c_30813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30809])).

tff(c_30814,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_30804])).

tff(c_30818,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_30814])).

tff(c_30822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30818])).

tff(c_30823,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_58593,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58590,c_30823])).

tff(c_58623,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58593])).

tff(c_58625,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_58623])).

tff(c_58628,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_58625])).

tff(c_58632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58628])).

tff(c_58633,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58623])).

tff(c_58635,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58633])).

tff(c_58638,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30918,c_58635])).

tff(c_58642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58638])).

tff(c_58643,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58633])).

tff(c_58647,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_58643])).

tff(c_58651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:43:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.19/15.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.19/15.57  
% 27.19/15.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.19/15.57  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 27.19/15.57  
% 27.19/15.57  %Foreground sorts:
% 27.19/15.57  
% 27.19/15.57  
% 27.19/15.57  %Background operators:
% 27.19/15.57  
% 27.19/15.57  
% 27.19/15.57  %Foreground operators:
% 27.19/15.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.19/15.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.19/15.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 27.19/15.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.19/15.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 27.19/15.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.19/15.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.19/15.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 27.19/15.57  tff('#skF_2', type, '#skF_2': $i).
% 27.19/15.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.19/15.57  tff('#skF_3', type, '#skF_3': $i).
% 27.19/15.57  tff('#skF_1', type, '#skF_1': $i).
% 27.19/15.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.19/15.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.19/15.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.19/15.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.19/15.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.19/15.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.19/15.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.19/15.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.19/15.57  
% 27.19/15.58  tff(f_86, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 27.19/15.58  tff(f_58, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 27.19/15.58  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 27.19/15.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.19/15.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.19/15.58  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 27.19/15.58  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 27.19/15.58  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 27.19/15.58  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 27.19/15.58  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.19/15.58  tff(c_22, plain, (![A_22, B_23]: (v1_relat_1(k7_relat_1(A_22, B_23)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.19/15.58  tff(c_30895, plain, (![C_549, A_550, B_551]: (k3_xboole_0(k7_relat_1(C_549, A_550), k7_relat_1(C_549, B_551))=k7_relat_1(C_549, k3_xboole_0(A_550, B_551)) | ~v1_relat_1(C_549))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.19/15.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.19/15.58  tff(c_96, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.19/15.58  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.19/15.58  tff(c_114, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6])).
% 27.19/15.58  tff(c_117, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 27.19/15.58  tff(c_30918, plain, (![C_549, A_550, B_551]: (r1_tarski(k7_relat_1(C_549, k3_xboole_0(A_550, B_551)), k7_relat_1(C_549, B_551)) | ~v1_relat_1(C_549))), inference(superposition, [status(thm), theory('equality')], [c_30895, c_117])).
% 27.19/15.58  tff(c_28, plain, (![B_31, A_30]: (k2_relat_1(k7_relat_1(B_31, A_30))=k9_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.19/15.58  tff(c_30830, plain, (![A_542, B_543]: (r1_tarski(k2_relat_1(A_542), k2_relat_1(B_543)) | ~r1_tarski(A_542, B_543) | ~v1_relat_1(B_543) | ~v1_relat_1(A_542))), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.19/15.58  tff(c_32585, plain, (![B_628, A_629, B_630]: (r1_tarski(k9_relat_1(B_628, A_629), k2_relat_1(B_630)) | ~r1_tarski(k7_relat_1(B_628, A_629), B_630) | ~v1_relat_1(B_630) | ~v1_relat_1(k7_relat_1(B_628, A_629)) | ~v1_relat_1(B_628))), inference(superposition, [status(thm), theory('equality')], [c_28, c_30830])).
% 27.19/15.58  tff(c_58590, plain, (![B_970, A_971, B_972, A_973]: (r1_tarski(k9_relat_1(B_970, A_971), k9_relat_1(B_972, A_973)) | ~r1_tarski(k7_relat_1(B_970, A_971), k7_relat_1(B_972, A_973)) | ~v1_relat_1(k7_relat_1(B_972, A_973)) | ~v1_relat_1(k7_relat_1(B_970, A_971)) | ~v1_relat_1(B_970) | ~v1_relat_1(B_972))), inference(superposition, [status(thm), theory('equality')], [c_28, c_32585])).
% 27.19/15.58  tff(c_417, plain, (![C_91, A_92, B_93]: (k3_xboole_0(k7_relat_1(C_91, A_92), k7_relat_1(C_91, B_93))=k7_relat_1(C_91, k3_xboole_0(A_92, B_93)) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.19/15.58  tff(c_105, plain, (![A_49, B_50]: (r1_tarski(k3_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6])).
% 27.19/15.58  tff(c_443, plain, (![C_91, A_92, B_93]: (r1_tarski(k7_relat_1(C_91, k3_xboole_0(A_92, B_93)), k7_relat_1(C_91, A_92)) | ~v1_relat_1(C_91))), inference(superposition, [status(thm), theory('equality')], [c_417, c_105])).
% 27.19/15.58  tff(c_291, plain, (![A_82, B_83]: (r1_tarski(k2_relat_1(A_82), k2_relat_1(B_83)) | ~r1_tarski(A_82, B_83) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.19/15.58  tff(c_2233, plain, (![B_172, A_173, B_174]: (r1_tarski(k9_relat_1(B_172, A_173), k2_relat_1(B_174)) | ~r1_tarski(k7_relat_1(B_172, A_173), B_174) | ~v1_relat_1(B_174) | ~v1_relat_1(k7_relat_1(B_172, A_173)) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_28, c_291])).
% 27.19/15.58  tff(c_30761, plain, (![B_538, A_539, B_540, A_541]: (r1_tarski(k9_relat_1(B_538, A_539), k9_relat_1(B_540, A_541)) | ~r1_tarski(k7_relat_1(B_538, A_539), k7_relat_1(B_540, A_541)) | ~v1_relat_1(k7_relat_1(B_540, A_541)) | ~v1_relat_1(k7_relat_1(B_538, A_539)) | ~v1_relat_1(B_538) | ~v1_relat_1(B_540))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2233])).
% 27.19/15.58  tff(c_248, plain, (![A_74, B_75, C_76]: (r1_tarski(A_74, k3_xboole_0(B_75, C_76)) | ~r1_tarski(A_74, C_76) | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.19/15.58  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.19/15.58  tff(c_262, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_248, c_34])).
% 27.19/15.58  tff(c_290, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_262])).
% 27.19/15.58  tff(c_30764, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30761, c_290])).
% 27.19/15.58  tff(c_30794, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30764])).
% 27.19/15.58  tff(c_30796, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_30794])).
% 27.19/15.58  tff(c_30799, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_30796])).
% 27.19/15.58  tff(c_30803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_30799])).
% 27.19/15.58  tff(c_30804, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_30794])).
% 27.19/15.58  tff(c_30806, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_30804])).
% 27.19/15.58  tff(c_30809, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_443, c_30806])).
% 27.19/15.58  tff(c_30813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_30809])).
% 27.19/15.58  tff(c_30814, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_30804])).
% 27.19/15.58  tff(c_30818, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_30814])).
% 27.19/15.58  tff(c_30822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_30818])).
% 27.19/15.58  tff(c_30823, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_262])).
% 27.19/15.58  tff(c_58593, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58590, c_30823])).
% 27.19/15.58  tff(c_58623, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_58593])).
% 27.19/15.58  tff(c_58625, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_58623])).
% 27.19/15.58  tff(c_58628, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_58625])).
% 27.19/15.58  tff(c_58632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58628])).
% 27.19/15.58  tff(c_58633, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_58623])).
% 27.19/15.58  tff(c_58635, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_58633])).
% 27.19/15.58  tff(c_58638, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30918, c_58635])).
% 27.19/15.58  tff(c_58642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58638])).
% 27.19/15.58  tff(c_58643, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_58633])).
% 27.19/15.58  tff(c_58647, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_58643])).
% 27.19/15.59  tff(c_58651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58647])).
% 27.19/15.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.19/15.59  
% 27.19/15.59  Inference rules
% 27.19/15.59  ----------------------
% 27.19/15.59  #Ref     : 0
% 27.19/15.59  #Sup     : 16353
% 27.19/15.59  #Fact    : 0
% 27.19/15.59  #Define  : 0
% 27.19/15.59  #Split   : 6
% 27.19/15.59  #Chain   : 0
% 27.19/15.59  #Close   : 0
% 27.19/15.59  
% 27.19/15.59  Ordering : KBO
% 27.19/15.59  
% 27.19/15.59  Simplification rules
% 27.19/15.59  ----------------------
% 27.19/15.59  #Subsume      : 3862
% 27.19/15.59  #Demod        : 8744
% 27.19/15.59  #Tautology    : 1401
% 27.19/15.59  #SimpNegUnit  : 0
% 27.19/15.59  #BackRed      : 0
% 27.19/15.59  
% 27.19/15.59  #Partial instantiations: 0
% 27.19/15.59  #Strategies tried      : 1
% 27.19/15.59  
% 27.19/15.59  Timing (in seconds)
% 27.19/15.59  ----------------------
% 27.19/15.59  Preprocessing        : 0.31
% 27.19/15.59  Parsing              : 0.17
% 27.19/15.59  CNF conversion       : 0.02
% 27.19/15.59  Main loop            : 14.51
% 27.19/15.59  Inferencing          : 2.05
% 27.33/15.59  Reduction            : 8.37
% 27.33/15.59  Demodulation         : 7.76
% 27.33/15.59  BG Simplification    : 0.32
% 27.33/15.59  Subsumption          : 3.35
% 27.33/15.59  Abstraction          : 0.52
% 27.33/15.59  MUC search           : 0.00
% 27.33/15.59  Cooper               : 0.00
% 27.33/15.59  Total                : 14.85
% 27.33/15.59  Index Insertion      : 0.00
% 27.33/15.59  Index Deletion       : 0.00
% 27.33/15.59  Index Matching       : 0.00
% 27.33/15.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
