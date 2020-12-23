%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:57 EST 2020

% Result     : Theorem 20.05s
% Output     : CNFRefutation 20.15s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 191 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 403 expanded)
%              Number of equality atoms :   13 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [B_43,A_44] : k1_setfam_1(k2_tarski(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_88])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_15721,plain,(
    ! [C_531,A_532,B_533] :
      ( k3_xboole_0(k7_relat_1(C_531,A_532),k7_relat_1(C_531,B_533)) = k7_relat_1(C_531,k3_xboole_0(A_532,B_533))
      | ~ v1_relat_1(C_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15948,plain,(
    ! [C_560,A_561,B_562,B_563] :
      ( r1_tarski(k7_relat_1(C_560,k3_xboole_0(A_561,B_562)),B_563)
      | ~ r1_tarski(k7_relat_1(C_560,A_561),B_563)
      | ~ v1_relat_1(C_560) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15721,c_8])).

tff(c_16003,plain,(
    ! [C_560,B_43,A_44,B_563] :
      ( r1_tarski(k7_relat_1(C_560,k3_xboole_0(B_43,A_44)),B_563)
      | ~ r1_tarski(k7_relat_1(C_560,A_44),B_563)
      | ~ v1_relat_1(C_560) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_15948])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( k2_relat_1(k7_relat_1(B_26,A_25)) = k9_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_15480,plain,(
    ! [A_500,B_501] :
      ( r1_tarski(k2_relat_1(A_500),k2_relat_1(B_501))
      | ~ r1_tarski(A_500,B_501)
      | ~ v1_relat_1(B_501)
      | ~ v1_relat_1(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17552,plain,(
    ! [B_615,A_616,B_617] :
      ( r1_tarski(k9_relat_1(B_615,A_616),k2_relat_1(B_617))
      | ~ r1_tarski(k7_relat_1(B_615,A_616),B_617)
      | ~ v1_relat_1(B_617)
      | ~ v1_relat_1(k7_relat_1(B_615,A_616))
      | ~ v1_relat_1(B_615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15480])).

tff(c_33346,plain,(
    ! [B_894,A_895,B_896,A_897] :
      ( r1_tarski(k9_relat_1(B_894,A_895),k9_relat_1(B_896,A_897))
      | ~ r1_tarski(k7_relat_1(B_894,A_895),k7_relat_1(B_896,A_897))
      | ~ v1_relat_1(k7_relat_1(B_896,A_897))
      | ~ v1_relat_1(k7_relat_1(B_894,A_895))
      | ~ v1_relat_1(B_894)
      | ~ v1_relat_1(B_896) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_17552])).

tff(c_493,plain,(
    ! [C_112,A_113,B_114] :
      ( k3_xboole_0(k7_relat_1(C_112,A_113),k7_relat_1(C_112,B_114)) = k7_relat_1(C_112,k3_xboole_0(A_113,B_114))
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_528,plain,(
    ! [C_112,A_113,B_114,B_4] :
      ( r1_tarski(k7_relat_1(C_112,k3_xboole_0(A_113,B_114)),B_4)
      | ~ r1_tarski(k7_relat_1(C_112,A_113),B_4)
      | ~ v1_relat_1(C_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_8])).

tff(c_346,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k2_relat_1(A_90),k2_relat_1(B_91))
      | ~ r1_tarski(A_90,B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2957,plain,(
    ! [B_205,A_206,B_207] :
      ( r1_tarski(k9_relat_1(B_205,A_206),k2_relat_1(B_207))
      | ~ r1_tarski(k7_relat_1(B_205,A_206),B_207)
      | ~ v1_relat_1(B_207)
      | ~ v1_relat_1(k7_relat_1(B_205,A_206))
      | ~ v1_relat_1(B_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_346])).

tff(c_14988,plain,(
    ! [B_488,A_489,B_490,A_491] :
      ( r1_tarski(k9_relat_1(B_488,A_489),k9_relat_1(B_490,A_491))
      | ~ r1_tarski(k7_relat_1(B_488,A_489),k7_relat_1(B_490,A_491))
      | ~ v1_relat_1(k7_relat_1(B_490,A_491))
      | ~ v1_relat_1(k7_relat_1(B_488,A_489))
      | ~ v1_relat_1(B_488)
      | ~ v1_relat_1(B_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2957])).

tff(c_248,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(A_71,k3_xboole_0(B_72,C_73))
      | ~ r1_tarski(A_71,C_73)
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_271,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_248,c_34])).

tff(c_315,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_15029,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14988,c_315])).

tff(c_15061,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15029])).

tff(c_15067,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_15061])).

tff(c_15070,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_15067])).

tff(c_15074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15070])).

tff(c_15075,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15061])).

tff(c_15446,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_15075])).

tff(c_15449,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_528,c_15446])).

tff(c_15453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_15449])).

tff(c_15454,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15075])).

tff(c_15458,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_15454])).

tff(c_15462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15458])).

tff(c_15463,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_33403,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_33346,c_15463])).

tff(c_33448,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_33403])).

tff(c_55238,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_33448])).

tff(c_55241,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_55238])).

tff(c_55245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55241])).

tff(c_55246,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33448])).

tff(c_55705,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_55246])).

tff(c_55708,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16003,c_55705])).

tff(c_55715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_55708])).

tff(c_55716,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_55246])).

tff(c_55720,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_55716])).

tff(c_55724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.05/9.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.05/9.74  
% 20.05/9.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.15/9.74  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 20.15/9.74  
% 20.15/9.74  %Foreground sorts:
% 20.15/9.74  
% 20.15/9.74  
% 20.15/9.74  %Background operators:
% 20.15/9.74  
% 20.15/9.74  
% 20.15/9.74  %Foreground operators:
% 20.15/9.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.15/9.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.15/9.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.15/9.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.15/9.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.15/9.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.15/9.74  tff('#skF_2', type, '#skF_2': $i).
% 20.15/9.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 20.15/9.74  tff('#skF_3', type, '#skF_3': $i).
% 20.15/9.74  tff('#skF_1', type, '#skF_1': $i).
% 20.15/9.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.15/9.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.15/9.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.15/9.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.15/9.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.15/9.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.15/9.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.15/9.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.15/9.74  
% 20.15/9.76  tff(f_86, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 20.15/9.76  tff(f_62, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 20.15/9.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.15/9.76  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 20.15/9.76  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 20.15/9.76  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 20.15/9.76  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 20.15/9.76  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 20.15/9.76  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 20.15/9.76  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 20.15/9.76  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.15/9.76  tff(c_24, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.15/9.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.15/9.76  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.15/9.76  tff(c_88, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.15/9.76  tff(c_103, plain, (![B_43, A_44]: (k1_setfam_1(k2_tarski(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_12, c_88])).
% 20.15/9.76  tff(c_16, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.15/9.76  tff(c_109, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 20.15/9.76  tff(c_15721, plain, (![C_531, A_532, B_533]: (k3_xboole_0(k7_relat_1(C_531, A_532), k7_relat_1(C_531, B_533))=k7_relat_1(C_531, k3_xboole_0(A_532, B_533)) | ~v1_relat_1(C_531))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.15/9.76  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.15/9.76  tff(c_15948, plain, (![C_560, A_561, B_562, B_563]: (r1_tarski(k7_relat_1(C_560, k3_xboole_0(A_561, B_562)), B_563) | ~r1_tarski(k7_relat_1(C_560, A_561), B_563) | ~v1_relat_1(C_560))), inference(superposition, [status(thm), theory('equality')], [c_15721, c_8])).
% 20.15/9.76  tff(c_16003, plain, (![C_560, B_43, A_44, B_563]: (r1_tarski(k7_relat_1(C_560, k3_xboole_0(B_43, A_44)), B_563) | ~r1_tarski(k7_relat_1(C_560, A_44), B_563) | ~v1_relat_1(C_560))), inference(superposition, [status(thm), theory('equality')], [c_109, c_15948])).
% 20.15/9.76  tff(c_28, plain, (![B_26, A_25]: (k2_relat_1(k7_relat_1(B_26, A_25))=k9_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.15/9.76  tff(c_15480, plain, (![A_500, B_501]: (r1_tarski(k2_relat_1(A_500), k2_relat_1(B_501)) | ~r1_tarski(A_500, B_501) | ~v1_relat_1(B_501) | ~v1_relat_1(A_500))), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.15/9.76  tff(c_17552, plain, (![B_615, A_616, B_617]: (r1_tarski(k9_relat_1(B_615, A_616), k2_relat_1(B_617)) | ~r1_tarski(k7_relat_1(B_615, A_616), B_617) | ~v1_relat_1(B_617) | ~v1_relat_1(k7_relat_1(B_615, A_616)) | ~v1_relat_1(B_615))), inference(superposition, [status(thm), theory('equality')], [c_28, c_15480])).
% 20.15/9.76  tff(c_33346, plain, (![B_894, A_895, B_896, A_897]: (r1_tarski(k9_relat_1(B_894, A_895), k9_relat_1(B_896, A_897)) | ~r1_tarski(k7_relat_1(B_894, A_895), k7_relat_1(B_896, A_897)) | ~v1_relat_1(k7_relat_1(B_896, A_897)) | ~v1_relat_1(k7_relat_1(B_894, A_895)) | ~v1_relat_1(B_894) | ~v1_relat_1(B_896))), inference(superposition, [status(thm), theory('equality')], [c_28, c_17552])).
% 20.15/9.76  tff(c_493, plain, (![C_112, A_113, B_114]: (k3_xboole_0(k7_relat_1(C_112, A_113), k7_relat_1(C_112, B_114))=k7_relat_1(C_112, k3_xboole_0(A_113, B_114)) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.15/9.76  tff(c_528, plain, (![C_112, A_113, B_114, B_4]: (r1_tarski(k7_relat_1(C_112, k3_xboole_0(A_113, B_114)), B_4) | ~r1_tarski(k7_relat_1(C_112, A_113), B_4) | ~v1_relat_1(C_112))), inference(superposition, [status(thm), theory('equality')], [c_493, c_8])).
% 20.15/9.76  tff(c_346, plain, (![A_90, B_91]: (r1_tarski(k2_relat_1(A_90), k2_relat_1(B_91)) | ~r1_tarski(A_90, B_91) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.15/9.76  tff(c_2957, plain, (![B_205, A_206, B_207]: (r1_tarski(k9_relat_1(B_205, A_206), k2_relat_1(B_207)) | ~r1_tarski(k7_relat_1(B_205, A_206), B_207) | ~v1_relat_1(B_207) | ~v1_relat_1(k7_relat_1(B_205, A_206)) | ~v1_relat_1(B_205))), inference(superposition, [status(thm), theory('equality')], [c_28, c_346])).
% 20.15/9.76  tff(c_14988, plain, (![B_488, A_489, B_490, A_491]: (r1_tarski(k9_relat_1(B_488, A_489), k9_relat_1(B_490, A_491)) | ~r1_tarski(k7_relat_1(B_488, A_489), k7_relat_1(B_490, A_491)) | ~v1_relat_1(k7_relat_1(B_490, A_491)) | ~v1_relat_1(k7_relat_1(B_488, A_489)) | ~v1_relat_1(B_488) | ~v1_relat_1(B_490))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2957])).
% 20.15/9.76  tff(c_248, plain, (![A_71, B_72, C_73]: (r1_tarski(A_71, k3_xboole_0(B_72, C_73)) | ~r1_tarski(A_71, C_73) | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.15/9.76  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.15/9.76  tff(c_271, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_248, c_34])).
% 20.15/9.76  tff(c_315, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_271])).
% 20.15/9.76  tff(c_15029, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14988, c_315])).
% 20.15/9.76  tff(c_15061, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_15029])).
% 20.15/9.76  tff(c_15067, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_15061])).
% 20.15/9.76  tff(c_15070, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_15067])).
% 20.15/9.76  tff(c_15074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_15070])).
% 20.15/9.76  tff(c_15075, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_15061])).
% 20.15/9.76  tff(c_15446, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_15075])).
% 20.15/9.76  tff(c_15449, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_528, c_15446])).
% 20.15/9.76  tff(c_15453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_15449])).
% 20.15/9.76  tff(c_15454, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_15075])).
% 20.15/9.76  tff(c_15458, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_15454])).
% 20.15/9.76  tff(c_15462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_15458])).
% 20.15/9.76  tff(c_15463, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_271])).
% 20.15/9.76  tff(c_33403, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_33346, c_15463])).
% 20.15/9.76  tff(c_33448, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_33403])).
% 20.15/9.76  tff(c_55238, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_33448])).
% 20.15/9.76  tff(c_55241, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_55238])).
% 20.15/9.76  tff(c_55245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_55241])).
% 20.15/9.76  tff(c_55246, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33448])).
% 20.15/9.76  tff(c_55705, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_55246])).
% 20.15/9.76  tff(c_55708, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16003, c_55705])).
% 20.15/9.76  tff(c_55715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_55708])).
% 20.15/9.76  tff(c_55716, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_55246])).
% 20.15/9.76  tff(c_55720, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_55716])).
% 20.15/9.76  tff(c_55724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_55720])).
% 20.15/9.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.15/9.76  
% 20.15/9.76  Inference rules
% 20.15/9.76  ----------------------
% 20.15/9.76  #Ref     : 0
% 20.15/9.76  #Sup     : 15841
% 20.15/9.76  #Fact    : 0
% 20.15/9.76  #Define  : 0
% 20.15/9.76  #Split   : 8
% 20.15/9.76  #Chain   : 0
% 20.15/9.76  #Close   : 0
% 20.15/9.76  
% 20.15/9.76  Ordering : KBO
% 20.15/9.76  
% 20.15/9.76  Simplification rules
% 20.15/9.76  ----------------------
% 20.15/9.76  #Subsume      : 6397
% 20.15/9.76  #Demod        : 3438
% 20.15/9.76  #Tautology    : 1641
% 20.15/9.76  #SimpNegUnit  : 9
% 20.15/9.76  #BackRed      : 0
% 20.15/9.76  
% 20.15/9.76  #Partial instantiations: 0
% 20.15/9.76  #Strategies tried      : 1
% 20.15/9.76  
% 20.15/9.76  Timing (in seconds)
% 20.15/9.76  ----------------------
% 20.15/9.76  Preprocessing        : 0.33
% 20.15/9.76  Parsing              : 0.18
% 20.15/9.76  CNF conversion       : 0.02
% 20.15/9.76  Main loop            : 8.61
% 20.15/9.76  Inferencing          : 1.36
% 20.15/9.76  Reduction            : 2.58
% 20.15/9.76  Demodulation         : 2.14
% 20.15/9.76  BG Simplification    : 0.19
% 20.15/9.76  Subsumption          : 4.03
% 20.15/9.76  Abstraction          : 0.26
% 20.15/9.76  MUC search           : 0.00
% 20.15/9.76  Cooper               : 0.00
% 20.15/9.76  Total                : 8.98
% 20.15/9.76  Index Insertion      : 0.00
% 20.15/9.76  Index Deletion       : 0.00
% 20.15/9.76  Index Matching       : 0.00
% 20.15/9.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
