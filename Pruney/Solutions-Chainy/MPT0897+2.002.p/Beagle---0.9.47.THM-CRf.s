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
% DateTime   : Thu Dec  3 10:09:47 EST 2020

% Result     : Theorem 55.92s
% Output     : CNFRefutation 56.59s
% Verified   : 
% Statistics : Number of formulae       :  505 (4708 expanded)
%              Number of leaves         :   33 (1455 expanded)
%              Depth                    :   25
%              Number of atoms          :  805 (9333 expanded)
%              Number of equality atoms :  178 (4624 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_37])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_32])).

tff(c_14111,plain,(
    ! [A_975,B_976,C_977,D_978] : k2_zfmisc_1(k3_zfmisc_1(A_975,B_976,C_977),D_978) = k4_zfmisc_1(A_975,B_976,C_977,D_978) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13856,plain,(
    ! [A_944,B_945] :
      ( v1_xboole_0(k2_zfmisc_1(A_944,B_945))
      | ~ v1_xboole_0(B_945) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_13867,plain,(
    ! [A_946,B_947] :
      ( k2_zfmisc_1(A_946,B_947) = '#skF_1'
      | ~ v1_xboole_0(B_947) ) ),
    inference(resolution,[status(thm)],[c_13856,c_42])).

tff(c_13876,plain,(
    ! [A_946] : k2_zfmisc_1(A_946,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_13867])).

tff(c_14121,plain,(
    ! [A_975,B_976,C_977] : k4_zfmisc_1(A_975,B_976,C_977,'#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14111,c_13876])).

tff(c_1231,plain,(
    ! [A_381,B_382,C_383,D_384] : k2_zfmisc_1(k3_zfmisc_1(A_381,B_382,C_383),D_384) = k4_zfmisc_1(A_381,B_382,C_383,D_384) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    ! [A_36,B_37] :
      ( v1_xboole_0(k2_zfmisc_1(A_36,B_37))
      | ~ v1_xboole_0(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_43,B_44] :
      ( k2_zfmisc_1(A_43,B_44) = '#skF_1'
      | ~ v1_xboole_0(B_44) ) ),
    inference(resolution,[status(thm)],[c_62,c_42])).

tff(c_120,plain,(
    ! [A_43] : k2_zfmisc_1(A_43,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_1248,plain,(
    ! [A_381,B_382,C_383] : k4_zfmisc_1(A_381,B_382,C_383,'#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_120])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( v1_xboole_0(k2_zfmisc_1(A_4,B_5))
      | ~ v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1118,plain,(
    ! [A_369,B_370,C_371] : k2_zfmisc_1(k2_zfmisc_1(A_369,B_370),C_371) = k3_zfmisc_1(A_369,B_370,C_371) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1141,plain,(
    ! [A_369,B_370,C_371] :
      ( v1_xboole_0(k3_zfmisc_1(A_369,B_370,C_371))
      | ~ v1_xboole_0(k2_zfmisc_1(A_369,B_370)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_14])).

tff(c_34,plain,(
    k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_17,B_18)),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2717,plain,(
    ! [A_485,B_486,C_487,D_488] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_485,B_486,C_487,D_488)),k3_zfmisc_1(A_485,B_486,C_487)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_22])).

tff(c_2761,plain,(
    r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2717])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2847,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) = k3_zfmisc_1('#skF_6','#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_2761,c_6])).

tff(c_3179,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_2847])).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1259,plain,(
    ! [A_381,B_382,C_383,D_384] : v1_relat_1(k4_zfmisc_1(A_381,B_382,C_383,D_384)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_20])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1517,plain,(
    ! [A_415,B_416,C_417,D_418] :
      ( v1_xboole_0(k4_zfmisc_1(A_415,B_416,C_417,D_418))
      | ~ v1_xboole_0(D_418) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_12])).

tff(c_1541,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1517])).

tff(c_1615,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1541])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_zfmisc_1(k3_zfmisc_1(A_23,B_24,C_25),D_26) = k4_zfmisc_1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1300,plain,(
    ! [B_392,A_393,D_394,C_395] :
      ( ~ r1_tarski(k2_zfmisc_1(B_392,A_393),k2_zfmisc_1(D_394,C_395))
      | r1_tarski(B_392,D_394)
      | v1_xboole_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7022,plain,(
    ! [C_674,C_670,D_669,D_672,B_671,A_673] :
      ( ~ r1_tarski(k4_zfmisc_1(A_673,B_671,C_670,D_672),k2_zfmisc_1(D_669,C_674))
      | r1_tarski(k3_zfmisc_1(A_673,B_671,C_670),D_669)
      | v1_xboole_0(D_672) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1300])).

tff(c_7048,plain,(
    ! [D_669,C_674] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_669,C_674))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),D_669)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_7022])).

tff(c_7058,plain,(
    ! [D_675,C_676] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_675,C_676))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),D_675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_7048])).

tff(c_7080,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_7058])).

tff(c_7085,plain,(
    r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_7080])).

tff(c_7087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3179,c_7085])).

tff(c_7088,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) = k3_zfmisc_1('#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2847])).

tff(c_1257,plain,(
    ! [A_381,B_382,C_383,D_384] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_381,B_382,C_383,D_384)),k3_zfmisc_1(A_381,B_382,C_383)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_22])).

tff(c_7304,plain,(
    r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7088,c_1257])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_34,B_35] :
      ( v1_xboole_0(k2_zfmisc_1(A_34,B_35))
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_38,B_39] :
      ( k2_zfmisc_1(A_38,B_39) = '#skF_1'
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_56,c_42])).

tff(c_77,plain,(
    ! [B_40] : k2_zfmisc_1('#skF_1',B_40) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_67])).

tff(c_88,plain,(
    r1_tarski(k1_relat_1('#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_110,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_88,c_6])).

tff(c_160,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_76,plain,(
    ! [B_39] : k2_zfmisc_1('#skF_1',B_39) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_67])).

tff(c_586,plain,(
    ! [B_82,A_83,D_84,C_85] :
      ( ~ r1_tarski(k2_zfmisc_1(B_82,A_83),k2_zfmisc_1(D_84,C_85))
      | r1_tarski(B_82,D_84)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_608,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(B_82,k1_relat_1(k2_zfmisc_1(B_82,A_83)))
      | v1_xboole_0(A_83)
      | ~ v1_relat_1(k2_zfmisc_1(B_82,A_83)) ) ),
    inference(resolution,[status(thm)],[c_24,c_586])).

tff(c_821,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,k1_relat_1(k2_zfmisc_1(B_111,A_112)))
      | v1_xboole_0(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_608])).

tff(c_841,plain,(
    ! [B_39] :
      ( r1_tarski('#skF_1',k1_relat_1('#skF_1'))
      | v1_xboole_0(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_821])).

tff(c_847,plain,(
    ! [B_39] : v1_xboole_0(B_39) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_841])).

tff(c_915,plain,(
    ! [A_118] : A_118 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_42])).

tff(c_970,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_160])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_970])).

tff(c_1028,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_121,plain,(
    ! [A_45] : k2_zfmisc_1(A_45,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_135,plain,(
    ! [A_45] : r1_tarski(k1_relat_1('#skF_1'),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_22])).

tff(c_1030,plain,(
    ! [A_45] : r1_tarski('#skF_1',A_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_135])).

tff(c_1740,plain,(
    ! [A_442,A_443,B_444] :
      ( k2_zfmisc_1(A_442,k2_zfmisc_1(A_443,B_444)) = '#skF_1'
      | ~ v1_xboole_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_18,plain,(
    ! [A_8,B_12,C_13,D_14] :
      ( ~ r1_tarski(k2_zfmisc_1(A_8,B_12),k2_zfmisc_1(C_13,D_14))
      | r1_tarski(B_12,D_14)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1761,plain,(
    ! [A_443,D_14,B_444,A_442,C_13] :
      ( ~ r1_tarski('#skF_1',k2_zfmisc_1(C_13,D_14))
      | r1_tarski(k2_zfmisc_1(A_443,B_444),D_14)
      | v1_xboole_0(A_442)
      | ~ v1_xboole_0(A_443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_18])).

tff(c_1842,plain,(
    ! [A_443,B_444,D_14,A_442] :
      ( r1_tarski(k2_zfmisc_1(A_443,B_444),D_14)
      | v1_xboole_0(A_442)
      | ~ v1_xboole_0(A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_1761])).

tff(c_2770,plain,(
    ! [A_489,B_490,D_491] :
      ( r1_tarski(k2_zfmisc_1(A_489,B_490),D_491)
      | ~ v1_xboole_0(A_489) ) ),
    inference(splitLeft,[status(thm)],[c_1842])).

tff(c_16,plain,(
    ! [B_12,A_8,D_14,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(B_12,A_8),k2_zfmisc_1(D_14,C_13))
      | r1_tarski(B_12,D_14)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2813,plain,(
    ! [A_489,D_14,B_490] :
      ( r1_tarski(A_489,D_14)
      | v1_xboole_0(B_490)
      | ~ v1_xboole_0(A_489) ) ),
    inference(resolution,[status(thm)],[c_2770,c_16])).

tff(c_2823,plain,(
    ! [A_492,D_493] :
      ( r1_tarski(A_492,D_493)
      | ~ v1_xboole_0(A_492) ) ),
    inference(splitLeft,[status(thm)],[c_2813])).

tff(c_2844,plain,(
    ! [D_493,A_492] :
      ( D_493 = A_492
      | ~ r1_tarski(D_493,A_492)
      | ~ v1_xboole_0(A_492) ) ),
    inference(resolution,[status(thm)],[c_2823,c_6])).

tff(c_7318,plain,
    ( k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7304,c_2844])).

tff(c_8674,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7318])).

tff(c_8681,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1141,c_8674])).

tff(c_8689,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_8681])).

tff(c_30,plain,
    ( '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2536,plain,(
    ! [A_477,B_478,C_479,D_480] :
      ( v1_xboole_0(k4_zfmisc_1(A_477,B_478,C_479,D_480))
      | ~ v1_xboole_0(k3_zfmisc_1(A_477,B_478,C_479)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_14])).

tff(c_2568,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2536])).

tff(c_2700,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2568])).

tff(c_2707,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1141,c_2700])).

tff(c_2715,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_2707])).

tff(c_1138,plain,(
    ! [A_369,B_370,C_371] :
      ( v1_xboole_0(k3_zfmisc_1(A_369,B_370,C_371))
      | ~ v1_xboole_0(C_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_12])).

tff(c_8682,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1138,c_8674])).

tff(c_2708,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1138,c_2700])).

tff(c_118,plain,(
    ! [A_43,A_4,B_5] :
      ( k2_zfmisc_1(A_43,k2_zfmisc_1(A_4,B_5)) = '#skF_1'
      | ~ v1_xboole_0(B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_111])).

tff(c_1467,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( ~ r1_tarski(k2_zfmisc_1(A_411,B_412),k2_zfmisc_1(C_413,D_414))
      | r1_tarski(B_412,D_414)
      | v1_xboole_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1482,plain,(
    ! [B_5,C_413,A_4,D_414,A_43] :
      ( ~ r1_tarski('#skF_1',k2_zfmisc_1(C_413,D_414))
      | r1_tarski(k2_zfmisc_1(A_4,B_5),D_414)
      | v1_xboole_0(A_43)
      | ~ v1_xboole_0(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_1467])).

tff(c_1507,plain,(
    ! [A_4,B_5,D_414,A_43] :
      ( r1_tarski(k2_zfmisc_1(A_4,B_5),D_414)
      | v1_xboole_0(A_43)
      | ~ v1_xboole_0(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_1482])).

tff(c_7091,plain,(
    ! [A_677,B_678,D_679] :
      ( r1_tarski(k2_zfmisc_1(A_677,B_678),D_679)
      | ~ v1_xboole_0(B_678) ) ),
    inference(splitLeft,[status(thm)],[c_1507])).

tff(c_7121,plain,(
    ! [A_23,B_24,D_26,C_25,D_679] :
      ( r1_tarski(k4_zfmisc_1(A_23,B_24,C_25,D_26),D_679)
      | ~ v1_xboole_0(D_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7091])).

tff(c_10510,plain,(
    ! [D_827,A_831,B_829,C_828,D_830,C_832] :
      ( ~ r1_tarski(k4_zfmisc_1(A_831,B_829,C_828,D_830),k2_zfmisc_1(D_827,C_832))
      | r1_tarski(k3_zfmisc_1(A_831,B_829,C_828),D_827)
      | v1_xboole_0(D_830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1300])).

tff(c_10584,plain,(
    ! [D_827,C_832] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_827,C_832))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),D_827)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10510])).

tff(c_10621,plain,(
    ! [D_833,C_834] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_833,C_834))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),D_833) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_10584])).

tff(c_10662,plain,(
    ! [D_833] :
      ( r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),D_833)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7121,c_10621])).

tff(c_10667,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10662])).

tff(c_10854,plain,(
    ! [B_844,B_846,D_845,A_847,A_848,C_843] :
      ( ~ r1_tarski(k2_zfmisc_1(B_846,A_848),k4_zfmisc_1(A_847,B_844,C_843,D_845))
      | r1_tarski(B_846,k3_zfmisc_1(A_847,B_844,C_843))
      | v1_xboole_0(A_848) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1300])).

tff(c_10959,plain,(
    ! [B_849,A_850] :
      ( ~ r1_tarski(k2_zfmisc_1(B_849,A_850),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(B_849,k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
      | v1_xboole_0(A_850) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10854])).

tff(c_12327,plain,(
    ! [A_909,B_910,C_911,D_912] :
      ( ~ r1_tarski(k4_zfmisc_1(A_909,B_910,C_911,D_912),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(k3_zfmisc_1(A_909,B_910,C_911),k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
      | v1_xboole_0(D_912) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10959])).

tff(c_12377,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_12327])).

tff(c_12409,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_10667,c_12377])).

tff(c_12727,plain,
    ( k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12409,c_6])).

tff(c_12731,plain,(
    k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7304,c_12727])).

tff(c_26,plain,(
    ! [A_20,B_21,C_22] : k2_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22) = k3_zfmisc_1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1322,plain,(
    ! [B_392,A_393] :
      ( r1_tarski(B_392,k1_relat_1(k2_zfmisc_1(B_392,A_393)))
      | v1_xboole_0(A_393)
      | ~ v1_relat_1(k2_zfmisc_1(B_392,A_393)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1300])).

tff(c_1551,plain,(
    ! [B_419,A_420] :
      ( r1_tarski(B_419,k1_relat_1(k2_zfmisc_1(B_419,A_420)))
      | v1_xboole_0(A_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1322])).

tff(c_1553,plain,(
    ! [B_419,A_420] :
      ( k1_relat_1(k2_zfmisc_1(B_419,A_420)) = B_419
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(B_419,A_420)),B_419)
      | v1_xboole_0(A_420) ) ),
    inference(resolution,[status(thm)],[c_1551,c_6])).

tff(c_1575,plain,(
    ! [B_421,A_422] :
      ( k1_relat_1(k2_zfmisc_1(B_421,A_422)) = B_421
      | v1_xboole_0(A_422) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1553])).

tff(c_1596,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relat_1(k3_zfmisc_1(A_20,B_21,C_22)) = k2_zfmisc_1(A_20,B_21)
      | v1_xboole_0(C_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1575])).

tff(c_12792,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) = k2_zfmisc_1('#skF_6','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12731,c_1596])).

tff(c_12828,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) = k2_zfmisc_1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2708,c_12792])).

tff(c_12856,plain,
    ( k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12828,c_1596])).

tff(c_12877,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_8682,c_12856])).

tff(c_1571,plain,(
    ! [B_419,A_420] :
      ( k1_relat_1(k2_zfmisc_1(B_419,A_420)) = B_419
      | v1_xboole_0(A_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1553])).

tff(c_12995,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_6'
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12877,c_1571])).

tff(c_13042,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2715,c_12995])).

tff(c_13063,plain,
    ( '#skF_6' = '#skF_2'
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13042,c_1571])).

tff(c_13087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8689,c_61,c_13063])).

tff(c_13089,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10662])).

tff(c_13132,plain,(
    '#skF_5' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_13089,c_42])).

tff(c_13143,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13132,c_48])).

tff(c_13155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_13143])).

tff(c_13157,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7318])).

tff(c_13200,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_13157,c_42])).

tff(c_13202,plain,(
    r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13200,c_7304])).

tff(c_1035,plain,(
    ! [A_363] : r1_tarski('#skF_1',A_363) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_135])).

tff(c_1038,plain,(
    ! [A_363] :
      ( A_363 = '#skF_1'
      | ~ r1_tarski(A_363,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1035,c_6])).

tff(c_13264,plain,(
    k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_13202,c_1038])).

tff(c_13270,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13264,c_2700])).

tff(c_13274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_13270])).

tff(c_13275,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2568])).

tff(c_13403,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_13275,c_42])).

tff(c_13414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_13403])).

tff(c_13416,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1541])).

tff(c_13429,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13416,c_42])).

tff(c_13448,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13429,c_48])).

tff(c_13434,plain,(
    ! [A_381,B_382,C_383] : k4_zfmisc_1(A_381,B_382,C_383,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13429,c_13429,c_1248])).

tff(c_13847,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13434,c_34])).

tff(c_13849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13448,c_13847])).

tff(c_13850,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4'
    | '#skF_5' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_13866,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_13850])).

tff(c_13851,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_13861,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13851,c_34])).

tff(c_15166,plain,(
    ! [A_1057,B_1058,C_1059,D_1060] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_1057,B_1058,C_1059,D_1060)),k3_zfmisc_1(A_1057,B_1058,C_1059)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14111,c_22])).

tff(c_15198,plain,(
    r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')),k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_15166])).

tff(c_15405,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) = k3_zfmisc_1('#skF_2','#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_15198,c_6])).

tff(c_15797,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_15405])).

tff(c_14132,plain,(
    ! [A_975,B_976,C_977,D_978] : v1_relat_1(k4_zfmisc_1(A_975,B_976,C_977,D_978)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14111,c_20])).

tff(c_14306,plain,(
    ! [A_1000,B_1001,C_1002,D_1003] :
      ( v1_xboole_0(k4_zfmisc_1(A_1000,B_1001,C_1002,D_1003))
      | ~ v1_xboole_0(D_1003) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14111,c_12])).

tff(c_14330,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_14306])).

tff(c_14340,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_14330])).

tff(c_14213,plain,(
    ! [B_992,A_993,D_994,C_995] :
      ( ~ r1_tarski(k2_zfmisc_1(B_992,A_993),k2_zfmisc_1(D_994,C_995))
      | r1_tarski(B_992,D_994)
      | v1_xboole_0(A_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20183,plain,(
    ! [D_1284,C_1283,A_1288,B_1285,D_1286,C_1287] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1288,B_1285,C_1283,D_1286),k2_zfmisc_1(D_1284,C_1287))
      | r1_tarski(k3_zfmisc_1(A_1288,B_1285,C_1283),D_1284)
      | v1_xboole_0(D_1286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14213])).

tff(c_20263,plain,(
    ! [D_1284,C_1287] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_1284,C_1287))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_1284)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_20183])).

tff(c_20294,plain,(
    ! [D_1289,C_1290] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_1289,C_1290))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_1289) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14340,c_20263])).

tff(c_20325,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')))
    | ~ v1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_20294])).

tff(c_20339,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14132,c_20325])).

tff(c_20341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15797,c_20339])).

tff(c_20342,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) = k3_zfmisc_1('#skF_2','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_15405])).

tff(c_14130,plain,(
    ! [A_975,B_976,C_977,D_978] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_975,B_976,C_977,D_978)),k3_zfmisc_1(A_975,B_976,C_977)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14111,c_22])).

tff(c_20683,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20342,c_14130])).

tff(c_13877,plain,(
    ! [A_948] : k2_zfmisc_1(A_948,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_13867])).

tff(c_13888,plain,(
    ! [A_948] : r1_tarski(k1_relat_1('#skF_1'),A_948) ),
    inference(superposition,[status(thm),theory(equality)],[c_13877,c_22])).

tff(c_13912,plain,(
    ! [A_952,B_953] :
      ( k2_zfmisc_1(A_952,B_953) = '#skF_1'
      | ~ v1_xboole_0(A_952) ) ),
    inference(resolution,[status(thm)],[c_56,c_42])).

tff(c_13921,plain,(
    ! [B_953] : k2_zfmisc_1('#skF_1',B_953) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_13912])).

tff(c_14223,plain,(
    ! [B_992,A_993] :
      ( r1_tarski(B_992,k1_relat_1(k2_zfmisc_1(B_992,A_993)))
      | v1_xboole_0(A_993)
      | ~ v1_relat_1(k2_zfmisc_1(B_992,A_993)) ) ),
    inference(resolution,[status(thm)],[c_24,c_14213])).

tff(c_14341,plain,(
    ! [B_1004,A_1005] :
      ( r1_tarski(B_1004,k1_relat_1(k2_zfmisc_1(B_1004,A_1005)))
      | v1_xboole_0(A_1005) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14223])).

tff(c_14355,plain,(
    ! [B_953] :
      ( r1_tarski('#skF_1',k1_relat_1('#skF_1'))
      | v1_xboole_0(B_953) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13921,c_14341])).

tff(c_14364,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_14355])).

tff(c_14369,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14364,c_6])).

tff(c_14373,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13888,c_14369])).

tff(c_14377,plain,(
    ! [A_948] : r1_tarski('#skF_1',A_948) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14373,c_13888])).

tff(c_14625,plain,(
    ! [A_1023,A_1024,B_1025] :
      ( k2_zfmisc_1(A_1023,k2_zfmisc_1(A_1024,B_1025)) = '#skF_1'
      | ~ v1_xboole_0(A_1024) ) ),
    inference(resolution,[status(thm)],[c_14,c_13867])).

tff(c_14646,plain,(
    ! [A_1024,D_14,B_1025,C_13,A_1023] :
      ( ~ r1_tarski('#skF_1',k2_zfmisc_1(C_13,D_14))
      | r1_tarski(k2_zfmisc_1(A_1024,B_1025),D_14)
      | v1_xboole_0(A_1023)
      | ~ v1_xboole_0(A_1024) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14625,c_18])).

tff(c_14725,plain,(
    ! [A_1024,B_1025,D_14,A_1023] :
      ( r1_tarski(k2_zfmisc_1(A_1024,B_1025),D_14)
      | v1_xboole_0(A_1023)
      | ~ v1_xboole_0(A_1024) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14377,c_14646])).

tff(c_15745,plain,(
    ! [A_1083,B_1084,D_1085] :
      ( r1_tarski(k2_zfmisc_1(A_1083,B_1084),D_1085)
      | ~ v1_xboole_0(A_1083) ) ),
    inference(splitLeft,[status(thm)],[c_14725])).

tff(c_15789,plain,(
    ! [A_1083,D_14,B_1084] :
      ( r1_tarski(A_1083,D_14)
      | v1_xboole_0(B_1084)
      | ~ v1_xboole_0(A_1083) ) ),
    inference(resolution,[status(thm)],[c_15745,c_16])).

tff(c_20345,plain,(
    ! [A_1291,D_1292] :
      ( r1_tarski(A_1291,D_1292)
      | ~ v1_xboole_0(A_1291) ) ),
    inference(splitLeft,[status(thm)],[c_15789])).

tff(c_20366,plain,(
    ! [D_1292,A_1291] :
      ( D_1292 = A_1291
      | ~ r1_tarski(D_1292,A_1291)
      | ~ v1_xboole_0(A_1291) ) ),
    inference(resolution,[status(thm)],[c_20345,c_6])).

tff(c_20719,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20683,c_20366])).

tff(c_21270,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20719])).

tff(c_14389,plain,(
    ! [A_1006,B_1007,C_1008,D_1009] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1006,B_1007),k2_zfmisc_1(C_1008,D_1009))
      | r1_tarski(B_1007,D_1009)
      | v1_xboole_0(A_1006) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22226,plain,(
    ! [C_1394,A_1399,B_1396,D_1398,B_1397,A_1395] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1395,B_1396),k4_zfmisc_1(A_1399,B_1397,C_1394,D_1398))
      | r1_tarski(B_1396,D_1398)
      | v1_xboole_0(A_1395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14389])).

tff(c_22309,plain,(
    ! [A_1400,B_1401] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1400,B_1401),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(B_1401,'#skF_9')
      | v1_xboole_0(A_1400) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_22226])).

tff(c_23358,plain,(
    ! [A_1438,B_1439,C_1440,D_1441] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1438,B_1439,C_1440,D_1441),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(D_1441,'#skF_9')
      | v1_xboole_0(k3_zfmisc_1(A_1438,B_1439,C_1440)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_22309])).

tff(c_23402,plain,
    ( r1_tarski('#skF_5','#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_23358])).

tff(c_23430,plain,(
    r1_tarski('#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_21270,c_23402])).

tff(c_23435,plain,
    ( '#skF_5' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_23430,c_6])).

tff(c_23440,plain,(
    ~ r1_tarski('#skF_9','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_13866,c_23435])).

tff(c_14523,plain,(
    ! [A_1020,A_1021,B_1022] :
      ( k2_zfmisc_1(A_1020,k2_zfmisc_1(A_1021,B_1022)) = '#skF_1'
      | ~ v1_xboole_0(B_1022) ) ),
    inference(resolution,[status(thm)],[c_12,c_13867])).

tff(c_14538,plain,(
    ! [A_1020,B_1022,A_1021,D_14,C_13] :
      ( ~ r1_tarski('#skF_1',k2_zfmisc_1(C_13,D_14))
      | r1_tarski(k2_zfmisc_1(A_1021,B_1022),D_14)
      | v1_xboole_0(A_1020)
      | ~ v1_xboole_0(B_1022) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14523,c_18])).

tff(c_14609,plain,(
    ! [A_1021,B_1022,D_14,A_1020] :
      ( r1_tarski(k2_zfmisc_1(A_1021,B_1022),D_14)
      | v1_xboole_0(A_1020)
      | ~ v1_xboole_0(B_1022) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14377,c_14538])).

tff(c_20722,plain,(
    ! [A_1317,B_1318,D_1319] :
      ( r1_tarski(k2_zfmisc_1(A_1317,B_1318),D_1319)
      | ~ v1_xboole_0(B_1318) ) ),
    inference(splitLeft,[status(thm)],[c_14609])).

tff(c_20755,plain,(
    ! [D_1319,A_23,B_24,D_26,C_25] :
      ( r1_tarski(k4_zfmisc_1(A_23,B_24,C_25,D_26),D_1319)
      | ~ v1_xboole_0(D_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_20722])).

tff(c_24071,plain,(
    ! [D_1466,C_1469,A_1470,D_1468,B_1467,C_1465] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1470,B_1467,C_1465,D_1468),k2_zfmisc_1(D_1466,C_1469))
      | r1_tarski(k3_zfmisc_1(A_1470,B_1467,C_1465),D_1466)
      | v1_xboole_0(D_1468) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14213])).

tff(c_24151,plain,(
    ! [D_1466,C_1469] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_1466,C_1469))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_1466)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_24071])).

tff(c_24182,plain,(
    ! [D_1471,C_1472] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(D_1471,C_1472))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_1471) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14340,c_24151])).

tff(c_24223,plain,(
    ! [D_1471] :
      ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_1471)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20755,c_24182])).

tff(c_24228,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24223])).

tff(c_24492,plain,(
    ! [A_1489,A_1488,B_1485,B_1486,C_1484,D_1487] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1486,A_1488),k4_zfmisc_1(A_1489,B_1485,C_1484,D_1487))
      | r1_tarski(B_1486,k3_zfmisc_1(A_1489,B_1485,C_1484))
      | v1_xboole_0(A_1488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14213])).

tff(c_24978,plain,(
    ! [B_1499,A_1500] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1499,A_1500),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(B_1499,k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
      | v1_xboole_0(A_1500) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_24492])).

tff(c_26428,plain,(
    ! [A_1557,B_1558,C_1559,D_1560] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1557,B_1558,C_1559,D_1560),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(k3_zfmisc_1(A_1557,B_1558,C_1559),k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
      | v1_xboole_0(D_1560) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24978])).

tff(c_26478,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_26428])).

tff(c_26510,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_24228,c_26478])).

tff(c_26515,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26510,c_6])).

tff(c_26519,plain,(
    k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20683,c_26515])).

tff(c_26601,plain,(
    ! [D_26] : k2_zfmisc_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),D_26) = k4_zfmisc_1('#skF_2','#skF_7','#skF_8',D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_26519,c_28])).

tff(c_26618,plain,(
    ! [D_26] : k4_zfmisc_1('#skF_2','#skF_7','#skF_8',D_26) = k4_zfmisc_1('#skF_2','#skF_3','#skF_4',D_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26601])).

tff(c_31156,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26618,c_13861])).

tff(c_15406,plain,(
    ! [A_1069,B_1070,C_1071,D_1072] :
      ( v1_xboole_0(k4_zfmisc_1(A_1069,B_1070,C_1071,D_1072))
      | ~ v1_xboole_0(k3_zfmisc_1(A_1069,B_1070,C_1071)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14111,c_14])).

tff(c_15438,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_15406])).

tff(c_15564,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_15438])).

tff(c_24230,plain,(
    ! [D_1477,D_1474,C_1475,A_1478,C_1473,B_1476] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1478,B_1476,C_1473,D_1477),k2_zfmisc_1(C_1475,D_1474))
      | r1_tarski(D_1477,D_1474)
      | v1_xboole_0(k3_zfmisc_1(A_1478,B_1476,C_1473)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14389])).

tff(c_24310,plain,(
    ! [C_1475,D_1474] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(C_1475,D_1474))
      | r1_tarski('#skF_9',D_1474)
      | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_24230])).

tff(c_24417,plain,(
    ! [C_1482,D_1483] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(C_1482,D_1483))
      | r1_tarski('#skF_9',D_1483) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15564,c_24310])).

tff(c_24444,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k4_zfmisc_1(A_23,B_24,C_25,D_26))
      | r1_tarski('#skF_9',D_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24417])).

tff(c_43716,plain,(
    ! [A_1898,B_1899,C_1900,D_1901] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1898,B_1899,C_1900,D_1901))
      | r1_tarski('#skF_9',D_1901) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31156,c_24444])).

tff(c_43749,plain,
    ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | r1_tarski('#skF_9','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31156,c_43716])).

tff(c_43800,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_43749])).

tff(c_43802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23440,c_43800])).

tff(c_43804,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_24223])).

tff(c_43847,plain,(
    '#skF_5' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_43804,c_42])).

tff(c_43859,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43847,c_48])).

tff(c_43872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14121,c_43859])).

tff(c_43874,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20719])).

tff(c_43917,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_43874,c_42])).

tff(c_43919,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43917,c_20683])).

tff(c_43964,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = '#skF_1'
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_43919,c_20366])).

tff(c_43972,plain,(
    k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_43964])).

tff(c_44117,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43972,c_15564])).

tff(c_44121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44117])).

tff(c_44122,plain,(
    ! [B_1084] : v1_xboole_0(B_1084) ),
    inference(splitRight,[status(thm)],[c_15789])).

tff(c_13953,plain,(
    ! [A_955,B_956,C_957] : k2_zfmisc_1(k2_zfmisc_1(A_955,B_956),C_957) = k3_zfmisc_1(A_955,B_956,C_957) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13969,plain,(
    ! [A_955,B_956,C_957] :
      ( v1_xboole_0(k3_zfmisc_1(A_955,B_956,C_957))
      | ~ v1_xboole_0(k2_zfmisc_1(A_955,B_956)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13953,c_14])).

tff(c_15571,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_7')) ),
    inference(resolution,[status(thm)],[c_13969,c_15564])).

tff(c_15580,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_15571])).

tff(c_44191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44122,c_15580])).

tff(c_44192,plain,(
    ! [A_1023] : v1_xboole_0(A_1023) ),
    inference(splitRight,[status(thm)],[c_14725])).

tff(c_44259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44192,c_15580])).

tff(c_44260,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_15438])).

tff(c_44336,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44260,c_42])).

tff(c_44347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44336])).

tff(c_44348,plain,(
    ! [B_953] : v1_xboole_0(B_953) ),
    inference(splitRight,[status(thm)],[c_14355])).

tff(c_44371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44348,c_14340])).

tff(c_44373,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_14330])).

tff(c_44386,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_44373,c_42])).

tff(c_44404,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44386,c_48])).

tff(c_44372,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_14330])).

tff(c_44403,plain,(
    ! [A_1] :
      ( A_1 = '#skF_9'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44386,c_42])).

tff(c_44615,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_44372,c_44403])).

tff(c_44619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44404,c_44615])).

tff(c_44621,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_13850])).

tff(c_44623,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44621,c_48])).

tff(c_240038,plain,(
    ! [A_5788,B_5789,C_5790] : k2_zfmisc_1(k2_zfmisc_1(A_5788,B_5789),C_5790) = k3_zfmisc_1(A_5788,B_5789,C_5790) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_240054,plain,(
    ! [A_5788,B_5789,C_5790] :
      ( v1_xboole_0(k3_zfmisc_1(A_5788,B_5789,C_5790))
      | ~ v1_xboole_0(k2_zfmisc_1(A_5788,B_5789)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240038,c_14])).

tff(c_45534,plain,(
    ! [A_2497,B_2498,C_2499] : k2_zfmisc_1(k2_zfmisc_1(A_2497,B_2498),C_2499) = k3_zfmisc_1(A_2497,B_2498,C_2499) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45550,plain,(
    ! [A_2497,B_2498,C_2499] :
      ( v1_xboole_0(k3_zfmisc_1(A_2497,B_2498,C_2499))
      | ~ v1_xboole_0(k2_zfmisc_1(A_2497,B_2498)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45534,c_14])).

tff(c_44622,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44621,c_13861])).

tff(c_45665,plain,(
    ! [A_2512,B_2513,C_2514,D_2515] : k2_zfmisc_1(k3_zfmisc_1(A_2512,B_2513,C_2514),D_2515) = k4_zfmisc_1(A_2512,B_2513,C_2514,D_2515) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_47042,plain,(
    ! [A_2613,B_2614,C_2615,D_2616] :
      ( v1_xboole_0(k4_zfmisc_1(A_2613,B_2614,C_2615,D_2616))
      | ~ v1_xboole_0(k3_zfmisc_1(A_2613,B_2614,C_2615)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45665,c_14])).

tff(c_47074,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44622,c_47042])).

tff(c_47208,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_47074])).

tff(c_47215,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_7')) ),
    inference(resolution,[status(thm)],[c_45550,c_47208])).

tff(c_47224,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_47215])).

tff(c_44620,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13850])).

tff(c_44628,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44620])).

tff(c_45547,plain,(
    ! [A_2497,B_2498,C_2499] :
      ( v1_xboole_0(k3_zfmisc_1(A_2497,B_2498,C_2499))
      | ~ v1_xboole_0(C_2499) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45534,c_12])).

tff(c_46494,plain,(
    ! [A_2589,B_2590,C_2591,D_2592] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_2589,B_2590,C_2591,D_2592)),k3_zfmisc_1(A_2589,B_2590,C_2591)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45665,c_22])).

tff(c_46523,plain,(
    r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')),k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44622,c_46494])).

tff(c_46829,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) = k3_zfmisc_1('#skF_2','#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))) ),
    inference(resolution,[status(thm)],[c_46523,c_6])).

tff(c_47270,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_46829])).

tff(c_45686,plain,(
    ! [A_2512,B_2513,C_2514,D_2515] : v1_relat_1(k4_zfmisc_1(A_2512,B_2513,C_2514,D_2515)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45665,c_20])).

tff(c_45882,plain,(
    ! [B_2542,A_2543,D_2544,C_2545] :
      ( ~ r1_tarski(k2_zfmisc_1(B_2542,A_2543),k2_zfmisc_1(D_2544,C_2545))
      | r1_tarski(B_2542,D_2544)
      | v1_xboole_0(A_2543) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51292,plain,(
    ! [B_2825,D_2829,C_2824,C_2827,D_2826,A_2828] :
      ( ~ r1_tarski(k4_zfmisc_1(A_2828,B_2825,C_2824,D_2826),k2_zfmisc_1(D_2829,C_2827))
      | r1_tarski(k3_zfmisc_1(A_2828,B_2825,C_2824),D_2829)
      | v1_xboole_0(D_2826) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_45882])).

tff(c_51369,plain,(
    ! [D_2829,C_2827] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_2829,C_2827))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_2829)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44622,c_51292])).

tff(c_51495,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_51369])).

tff(c_51550,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_51495,c_42])).

tff(c_45943,plain,(
    ! [A_2548,B_2549,C_2550,D_2551] :
      ( v1_xboole_0(k4_zfmisc_1(A_2548,B_2549,C_2550,D_2551))
      | ~ v1_xboole_0(D_2551) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45665,c_12])).

tff(c_45971,plain,(
    ! [A_2548,B_2549,C_2550,D_2551] :
      ( k4_zfmisc_1(A_2548,B_2549,C_2550,D_2551) = '#skF_1'
      | ~ v1_xboole_0(D_2551) ) ),
    inference(resolution,[status(thm)],[c_45943,c_42])).

tff(c_51546,plain,(
    ! [A_2548,B_2549,C_2550] : k4_zfmisc_1(A_2548,B_2549,C_2550,'#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_51495,c_45971])).

tff(c_52430,plain,(
    ! [A_2548,B_2549,C_2550] : k4_zfmisc_1(A_2548,B_2549,C_2550,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51550,c_51546])).

tff(c_51598,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51550,c_44623])).

tff(c_52439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52430,c_51598])).

tff(c_53595,plain,(
    ! [D_2895,C_2896] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_2895,C_2896))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_2895) ) ),
    inference(splitRight,[status(thm)],[c_51369])).

tff(c_53632,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')))
    | ~ v1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(resolution,[status(thm)],[c_24,c_53595])).

tff(c_53646,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45686,c_53632])).

tff(c_53648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47270,c_53646])).

tff(c_53649,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) = k3_zfmisc_1('#skF_2','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_46829])).

tff(c_45684,plain,(
    ! [A_2512,B_2513,C_2514,D_2515] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_2512,B_2513,C_2514,D_2515)),k3_zfmisc_1(A_2512,B_2513,C_2514)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45665,c_22])).

tff(c_53975,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53649,c_45684])).

tff(c_44629,plain,(
    ! [A_1919,B_1920] :
      ( k2_zfmisc_1(A_1919,B_1920) = '#skF_1'
      | ~ v1_xboole_0(A_1919) ) ),
    inference(resolution,[status(thm)],[c_56,c_42])).

tff(c_44649,plain,(
    ! [B_1923] : k2_zfmisc_1('#skF_1',B_1923) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_44629])).

tff(c_44660,plain,(
    r1_tarski(k1_relat_1('#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44649,c_22])).

tff(c_44672,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44660,c_6])).

tff(c_44722,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44672])).

tff(c_44638,plain,(
    ! [B_1920] : k2_zfmisc_1('#skF_1',B_1920) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_44629])).

tff(c_45110,plain,(
    ! [B_1977,A_1978,D_1979,C_1980] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1977,A_1978),k2_zfmisc_1(D_1979,C_1980))
      | r1_tarski(B_1977,D_1979)
      | v1_xboole_0(A_1978) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45120,plain,(
    ! [B_1977,A_1978] :
      ( r1_tarski(B_1977,k1_relat_1(k2_zfmisc_1(B_1977,A_1978)))
      | v1_xboole_0(A_1978)
      | ~ v1_relat_1(k2_zfmisc_1(B_1977,A_1978)) ) ),
    inference(resolution,[status(thm)],[c_24,c_45110])).

tff(c_45366,plain,(
    ! [B_2251,A_2252] :
      ( r1_tarski(B_2251,k1_relat_1(k2_zfmisc_1(B_2251,A_2252)))
      | v1_xboole_0(A_2252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_45120])).

tff(c_45383,plain,(
    ! [B_1920] :
      ( r1_tarski('#skF_1',k1_relat_1('#skF_1'))
      | v1_xboole_0(B_1920) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44638,c_45366])).

tff(c_45389,plain,(
    ! [B_1920] : v1_xboole_0(B_1920) ),
    inference(negUnitSimplification,[status(thm)],[c_44722,c_45383])).

tff(c_45412,plain,(
    ! [A_2254] : A_2254 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45389,c_42])).

tff(c_45467,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45412,c_44722])).

tff(c_45526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45467])).

tff(c_45527,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44672])).

tff(c_44677,plain,(
    ! [A_1924,B_1925] :
      ( k2_zfmisc_1(A_1924,B_1925) = '#skF_1'
      | ~ v1_xboole_0(B_1925) ) ),
    inference(resolution,[status(thm)],[c_13856,c_42])).

tff(c_44687,plain,(
    ! [A_1926] : k2_zfmisc_1(A_1926,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_44677])).

tff(c_44701,plain,(
    ! [A_1926] : r1_tarski(k1_relat_1('#skF_1'),A_1926) ),
    inference(superposition,[status(thm),theory(equality)],[c_44687,c_22])).

tff(c_45529,plain,(
    ! [A_1926] : r1_tarski('#skF_1',A_1926) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45527,c_44701])).

tff(c_46238,plain,(
    ! [A_2576,A_2577,B_2578] :
      ( k2_zfmisc_1(A_2576,k2_zfmisc_1(A_2577,B_2578)) = '#skF_1'
      | ~ v1_xboole_0(B_2578) ) ),
    inference(resolution,[status(thm)],[c_12,c_44677])).

tff(c_46271,plain,(
    ! [B_2578,D_14,A_2576,A_2577,C_13] :
      ( ~ r1_tarski('#skF_1',k2_zfmisc_1(C_13,D_14))
      | r1_tarski(k2_zfmisc_1(A_2577,B_2578),D_14)
      | v1_xboole_0(A_2576)
      | ~ v1_xboole_0(B_2578) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46238,c_18])).

tff(c_46344,plain,(
    ! [A_2577,B_2578,D_14,A_2576] :
      ( r1_tarski(k2_zfmisc_1(A_2577,B_2578),D_14)
      | v1_xboole_0(A_2576)
      | ~ v1_xboole_0(B_2578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45529,c_46271])).

tff(c_53652,plain,(
    ! [A_2897,B_2898,D_2899] :
      ( r1_tarski(k2_zfmisc_1(A_2897,B_2898),D_2899)
      | ~ v1_xboole_0(B_2898) ) ),
    inference(splitLeft,[status(thm)],[c_46344])).

tff(c_53695,plain,(
    ! [B_2898,D_14,A_2897] :
      ( r1_tarski(B_2898,D_14)
      | v1_xboole_0(A_2897)
      | ~ v1_xboole_0(B_2898) ) ),
    inference(resolution,[status(thm)],[c_53652,c_18])).

tff(c_53705,plain,(
    ! [B_2900,D_2901] :
      ( r1_tarski(B_2900,D_2901)
      | ~ v1_xboole_0(B_2900) ) ),
    inference(splitLeft,[status(thm)],[c_53695])).

tff(c_53726,plain,(
    ! [D_2901,B_2900] :
      ( D_2901 = B_2900
      | ~ r1_tarski(D_2901,B_2900)
      | ~ v1_xboole_0(B_2900) ) ),
    inference(resolution,[status(thm)],[c_53705,c_6])).

tff(c_54131,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_53975,c_53726])).

tff(c_54462,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54131])).

tff(c_54470,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_45547,c_54462])).

tff(c_47216,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_45547,c_47208])).

tff(c_56906,plain,(
    ! [B_3054,D_3058,C_3053,C_3056,A_3057,D_3055] :
      ( ~ r1_tarski(k4_zfmisc_1(A_3057,B_3054,C_3053,D_3055),k2_zfmisc_1(D_3058,C_3056))
      | r1_tarski(k3_zfmisc_1(A_3057,B_3054,C_3053),D_3058)
      | v1_xboole_0(D_3055) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_45882])).

tff(c_56980,plain,(
    ! [D_3058,C_3056] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_3058,C_3056))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_3058)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44622,c_56906])).

tff(c_57011,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_56980])).

tff(c_57054,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_57011,c_42])).

tff(c_57050,plain,(
    ! [A_2548,B_2549,C_2550] : k4_zfmisc_1(A_2548,B_2549,C_2550,'#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_57011,c_45971])).

tff(c_57866,plain,(
    ! [A_2548,B_2549,C_2550] : k4_zfmisc_1(A_2548,B_2549,C_2550,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57054,c_57050])).

tff(c_57100,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57054,c_44623])).

tff(c_57876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57866,c_57100])).

tff(c_57878,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_56980])).

tff(c_54132,plain,
    ( k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_53975,c_6])).

tff(c_55624,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_54132])).

tff(c_58228,plain,(
    ! [A_3108,A_3107,B_3105,B_3104,C_3103,D_3106] :
      ( ~ r1_tarski(k2_zfmisc_1(B_3105,A_3107),k4_zfmisc_1(A_3108,B_3104,C_3103,D_3106))
      | r1_tarski(B_3105,k3_zfmisc_1(A_3108,B_3104,C_3103))
      | v1_xboole_0(A_3107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_45882])).

tff(c_58333,plain,(
    ! [B_3109,A_3110] :
      ( ~ r1_tarski(k2_zfmisc_1(B_3109,A_3110),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(B_3109,k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
      | v1_xboole_0(A_3110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44622,c_58228])).

tff(c_60328,plain,(
    ! [A_3184,B_3185,C_3186,D_3187] :
      ( ~ r1_tarski(k4_zfmisc_1(A_3184,B_3185,C_3186,D_3187),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(k3_zfmisc_1(A_3184,B_3185,C_3186),k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
      | v1_xboole_0(D_3187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58333])).

tff(c_60381,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_60328])).

tff(c_60416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57878,c_55624,c_60381])).

tff(c_60417,plain,(
    k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54132])).

tff(c_45892,plain,(
    ! [B_2542,A_2543] :
      ( r1_tarski(B_2542,k1_relat_1(k2_zfmisc_1(B_2542,A_2543)))
      | v1_xboole_0(A_2543)
      | ~ v1_relat_1(k2_zfmisc_1(B_2542,A_2543)) ) ),
    inference(resolution,[status(thm)],[c_24,c_45882])).

tff(c_45977,plain,(
    ! [B_2552,A_2553] :
      ( r1_tarski(B_2552,k1_relat_1(k2_zfmisc_1(B_2552,A_2553)))
      | v1_xboole_0(A_2553) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_45892])).

tff(c_45979,plain,(
    ! [B_2552,A_2553] :
      ( k1_relat_1(k2_zfmisc_1(B_2552,A_2553)) = B_2552
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(B_2552,A_2553)),B_2552)
      | v1_xboole_0(A_2553) ) ),
    inference(resolution,[status(thm)],[c_45977,c_6])).

tff(c_45997,plain,(
    ! [B_2554,A_2555] :
      ( k1_relat_1(k2_zfmisc_1(B_2554,A_2555)) = B_2554
      | v1_xboole_0(A_2555) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_45979])).

tff(c_46018,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relat_1(k3_zfmisc_1(A_20,B_21,C_22)) = k2_zfmisc_1(A_20,B_21)
      | v1_xboole_0(C_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_45997])).

tff(c_60426,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) = k2_zfmisc_1('#skF_2','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_60417,c_46018])).

tff(c_60461,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) = k2_zfmisc_1('#skF_2','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_47216,c_60426])).

tff(c_60471,plain,
    ( k2_zfmisc_1('#skF_2','#skF_7') = k2_zfmisc_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60461,c_46018])).

tff(c_60483,plain,(
    k2_zfmisc_1('#skF_2','#skF_7') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54470,c_60471])).

tff(c_60570,plain,(
    ! [C_13,D_14] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1(C_13,D_14))
      | r1_tarski('#skF_7',D_14)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60483,c_18])).

tff(c_63793,plain,(
    ! [C_3296,D_3297] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1(C_3296,D_3297))
      | r1_tarski('#skF_7',D_3297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_47224,c_60570])).

tff(c_63852,plain,(
    r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_63793])).

tff(c_63857,plain,
    ( '#skF_7' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_7') ),
    inference(resolution,[status(thm)],[c_63852,c_6])).

tff(c_63862,plain,(
    ~ r1_tarski('#skF_3','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44628,c_63857])).

tff(c_238664,plain,(
    ! [A_5462,B_5463] :
      ( ~ r1_tarski(k2_zfmisc_1(A_5462,B_5463),k2_zfmisc_1('#skF_2','#skF_3'))
      | r1_tarski(B_5463,'#skF_7')
      | v1_xboole_0(A_5462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60483,c_18])).

tff(c_238890,plain,
    ( r1_tarski('#skF_3','#skF_7')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_238664])).

tff(c_239014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47224,c_63862,c_238890])).

tff(c_239016,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54131])).

tff(c_239059,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_239016,c_42])).

tff(c_239061,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239059,c_53975])).

tff(c_45576,plain,(
    ! [A_2500] : r1_tarski('#skF_1',A_2500) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45527,c_44701])).

tff(c_45579,plain,(
    ! [A_2500] :
      ( A_2500 = '#skF_1'
      | ~ r1_tarski(A_2500,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_45576,c_6])).

tff(c_239111,plain,(
    k3_zfmisc_1('#skF_2','#skF_7','#skF_8') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_239061,c_45579])).

tff(c_239251,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239111,c_47208])).

tff(c_239255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_239251])).

tff(c_239256,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_47074])).

tff(c_239332,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_239256,c_42])).

tff(c_239343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44623,c_239332])).

tff(c_239345,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44620])).

tff(c_239404,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239345,c_44622])).

tff(c_240169,plain,(
    ! [A_5803,B_5804,C_5805,D_5806] : k2_zfmisc_1(k3_zfmisc_1(A_5803,B_5804,C_5805),D_5806) = k4_zfmisc_1(A_5803,B_5804,C_5805,D_5806) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_241546,plain,(
    ! [A_5904,B_5905,C_5906,D_5907] :
      ( v1_xboole_0(k4_zfmisc_1(A_5904,B_5905,C_5906,D_5907))
      | ~ v1_xboole_0(k3_zfmisc_1(A_5904,B_5905,C_5906)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240169,c_14])).

tff(c_241578,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239404,c_241546])).

tff(c_241712,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_241578])).

tff(c_241719,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_240054,c_241712])).

tff(c_239344,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44620])).

tff(c_240386,plain,(
    ! [B_5833,A_5834,D_5835,C_5836] :
      ( ~ r1_tarski(k2_zfmisc_1(B_5833,A_5834),k2_zfmisc_1(D_5835,C_5836))
      | r1_tarski(B_5833,D_5835)
      | v1_xboole_0(A_5834) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250617,plain,(
    ! [D_6322,A_6323,C_6319,D_6321,C_6324,B_6320] :
      ( ~ r1_tarski(k4_zfmisc_1(A_6323,B_6320,C_6319,D_6321),k2_zfmisc_1(D_6322,C_6324))
      | r1_tarski(k3_zfmisc_1(A_6323,B_6320,C_6319),D_6322)
      | v1_xboole_0(D_6321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_240386])).

tff(c_250694,plain,(
    ! [D_6322,C_6324] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_6322,C_6324))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),D_6322)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239404,c_250617])).

tff(c_250727,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_250694])).

tff(c_250770,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_250727,c_42])).

tff(c_240447,plain,(
    ! [A_5839,B_5840,C_5841,D_5842] :
      ( v1_xboole_0(k4_zfmisc_1(A_5839,B_5840,C_5841,D_5842))
      | ~ v1_xboole_0(D_5842) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240169,c_12])).

tff(c_240475,plain,(
    ! [A_5839,B_5840,C_5841,D_5842] :
      ( k4_zfmisc_1(A_5839,B_5840,C_5841,D_5842) = '#skF_1'
      | ~ v1_xboole_0(D_5842) ) ),
    inference(resolution,[status(thm)],[c_240447,c_42])).

tff(c_250766,plain,(
    ! [A_5839,B_5840,C_5841] : k4_zfmisc_1(A_5839,B_5840,C_5841,'#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_250727,c_240475])).

tff(c_251586,plain,(
    ! [A_5839,B_5840,C_5841] : k4_zfmisc_1(A_5839,B_5840,C_5841,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250770,c_250766])).

tff(c_250817,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250770,c_44623])).

tff(c_251596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251586,c_250817])).

tff(c_251598,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_250694])).

tff(c_240998,plain,(
    ! [A_5880,B_5881,C_5882,D_5883] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_5880,B_5881,C_5882,D_5883)),k3_zfmisc_1(A_5880,B_5881,C_5882)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240169,c_22])).

tff(c_241027,plain,(
    r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')),k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239404,c_240998])).

tff(c_241333,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) = k3_zfmisc_1('#skF_2','#skF_3','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))) ),
    inference(resolution,[status(thm)],[c_241027,c_6])).

tff(c_241774,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_241333])).

tff(c_240190,plain,(
    ! [A_5803,B_5804,C_5805,D_5806] : v1_relat_1(k4_zfmisc_1(A_5803,B_5804,C_5805,D_5806)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240169,c_20])).

tff(c_240182,plain,(
    ! [A_5803,B_5804,C_5805,D_5806] :
      ( v1_xboole_0(k4_zfmisc_1(A_5803,B_5804,C_5805,D_5806))
      | ~ v1_xboole_0(D_5806) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240169,c_12])).

tff(c_239350,plain,(
    ! [A_5469,B_5470] :
      ( k2_zfmisc_1(A_5469,B_5470) = '#skF_1'
      | ~ v1_xboole_0(A_5469) ) ),
    inference(resolution,[status(thm)],[c_56,c_42])).

tff(c_239360,plain,(
    ! [B_5471] : k2_zfmisc_1('#skF_1',B_5471) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_239350])).

tff(c_239371,plain,(
    r1_tarski(k1_relat_1('#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_239360,c_22])).

tff(c_239393,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_239371,c_6])).

tff(c_239444,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_239393])).

tff(c_239359,plain,(
    ! [B_5470] : k2_zfmisc_1('#skF_1',B_5470) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_239350])).

tff(c_239681,plain,(
    ! [B_5510,A_5511,D_5512,C_5513] :
      ( ~ r1_tarski(k2_zfmisc_1(B_5510,A_5511),k2_zfmisc_1(D_5512,C_5513))
      | r1_tarski(B_5510,D_5512)
      | v1_xboole_0(A_5511) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_239691,plain,(
    ! [B_5510,A_5511] :
      ( r1_tarski(B_5510,k1_relat_1(k2_zfmisc_1(B_5510,A_5511)))
      | v1_xboole_0(A_5511)
      | ~ v1_relat_1(k2_zfmisc_1(B_5510,A_5511)) ) ),
    inference(resolution,[status(thm)],[c_24,c_239681])).

tff(c_239832,plain,(
    ! [B_5527,A_5528] :
      ( r1_tarski(B_5527,k1_relat_1(k2_zfmisc_1(B_5527,A_5528)))
      | v1_xboole_0(A_5528) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_239691])).

tff(c_239849,plain,(
    ! [B_5470] :
      ( r1_tarski('#skF_1',k1_relat_1('#skF_1'))
      | v1_xboole_0(B_5470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239359,c_239832])).

tff(c_239855,plain,(
    ! [B_5470] : v1_xboole_0(B_5470) ),
    inference(negUnitSimplification,[status(thm)],[c_239444,c_239849])).

tff(c_239916,plain,(
    ! [A_5534] : A_5534 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239855,c_42])).

tff(c_239971,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_239916,c_239444])).

tff(c_240030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_239971])).

tff(c_240031,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_239393])).

tff(c_239394,plain,(
    ! [A_5474,B_5475] :
      ( k2_zfmisc_1(A_5474,B_5475) = '#skF_1'
      | ~ v1_xboole_0(B_5475) ) ),
    inference(resolution,[status(thm)],[c_13856,c_42])).

tff(c_239409,plain,(
    ! [A_5476] : k2_zfmisc_1(A_5476,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_239394])).

tff(c_239423,plain,(
    ! [A_5476] : r1_tarski(k1_relat_1('#skF_1'),A_5476) ),
    inference(superposition,[status(thm),theory(equality)],[c_239409,c_22])).

tff(c_240033,plain,(
    ! [A_5476] : r1_tarski('#skF_1',A_5476) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240031,c_239423])).

tff(c_240742,plain,(
    ! [A_5867,A_5868,B_5869] :
      ( k2_zfmisc_1(A_5867,k2_zfmisc_1(A_5868,B_5869)) = '#skF_1'
      | ~ v1_xboole_0(A_5868) ) ),
    inference(resolution,[status(thm)],[c_14,c_239394])).

tff(c_240775,plain,(
    ! [A_5867,B_5869,D_14,A_5868,C_13] :
      ( ~ r1_tarski('#skF_1',k2_zfmisc_1(C_13,D_14))
      | r1_tarski(k2_zfmisc_1(A_5868,B_5869),D_14)
      | v1_xboole_0(A_5867)
      | ~ v1_xboole_0(A_5868) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240742,c_18])).

tff(c_240848,plain,(
    ! [A_5868,B_5869,D_14,A_5867] :
      ( r1_tarski(k2_zfmisc_1(A_5868,B_5869),D_14)
      | v1_xboole_0(A_5867)
      | ~ v1_xboole_0(A_5868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240033,c_240775])).

tff(c_241776,plain,(
    ! [A_5914,B_5915,D_5916] :
      ( r1_tarski(k2_zfmisc_1(A_5914,B_5915),D_5916)
      | ~ v1_xboole_0(A_5914) ) ),
    inference(splitLeft,[status(thm)],[c_240848])).

tff(c_241818,plain,(
    ! [A_5914,D_14,B_5915] :
      ( r1_tarski(A_5914,D_14)
      | v1_xboole_0(B_5915)
      | ~ v1_xboole_0(A_5914) ) ),
    inference(resolution,[status(thm)],[c_241776,c_16])).

tff(c_241828,plain,(
    ! [A_5914,D_14] :
      ( r1_tarski(A_5914,D_14)
      | ~ v1_xboole_0(A_5914) ) ),
    inference(splitLeft,[status(thm)],[c_241818])).

tff(c_240271,plain,(
    ! [A_5820,B_5821,C_5822,D_5823] :
      ( ~ r1_tarski(k2_zfmisc_1(A_5820,B_5821),k2_zfmisc_1(C_5822,D_5823))
      | r1_tarski(B_5821,D_5823)
      | v1_xboole_0(A_5820) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_245786,plain,(
    ! [D_6120,C_6119,A_6121,B_6118,C_6117,D_6122] :
      ( ~ r1_tarski(k4_zfmisc_1(A_6121,B_6118,C_6117,D_6120),k2_zfmisc_1(C_6119,D_6122))
      | r1_tarski(D_6120,D_6122)
      | v1_xboole_0(k3_zfmisc_1(A_6121,B_6118,C_6117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_240271])).

tff(c_245863,plain,(
    ! [C_6119,D_6122] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(C_6119,D_6122))
      | r1_tarski('#skF_9',D_6122)
      | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239404,c_245786])).

tff(c_245943,plain,(
    ! [C_6126,D_6127] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(C_6126,D_6127))
      | r1_tarski('#skF_9',D_6127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_241712,c_245863])).

tff(c_245985,plain,(
    ! [D_6127] :
      ( r1_tarski('#skF_9',D_6127)
      | ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_241828,c_245943])).

tff(c_245996,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_245985])).

tff(c_246004,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_240182,c_245996])).

tff(c_246013,plain,(
    ! [D_6131,A_6132,D_6130,C_6133,C_6128,B_6129] :
      ( ~ r1_tarski(k4_zfmisc_1(A_6132,B_6129,C_6128,D_6130),k2_zfmisc_1(D_6131,C_6133))
      | r1_tarski(k3_zfmisc_1(A_6132,B_6129,C_6128),D_6131)
      | v1_xboole_0(D_6130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_240386])).

tff(c_246090,plain,(
    ! [D_6131,C_6133] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_6131,C_6133))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),D_6131)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239404,c_246013])).

tff(c_246133,plain,(
    ! [D_6134,C_6135] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_6134,C_6135))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),D_6134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_246004,c_246090])).

tff(c_246164,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')))
    | ~ v1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(resolution,[status(thm)],[c_24,c_246133])).

tff(c_246178,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240190,c_246164])).

tff(c_246180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241774,c_246178])).

tff(c_246185,plain,(
    ! [D_6136] : r1_tarski('#skF_9',D_6136) ),
    inference(splitRight,[status(thm)],[c_245985])).

tff(c_240080,plain,(
    ! [A_5791] : r1_tarski('#skF_1',A_5791) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240031,c_239423])).

tff(c_240083,plain,(
    ! [A_5791] :
      ( A_5791 = '#skF_1'
      | ~ r1_tarski(A_5791,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_240080,c_6])).

tff(c_246201,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_246185,c_240083])).

tff(c_246250,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246201,c_44623])).

tff(c_246182,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_245985])).

tff(c_246251,plain,(
    ! [A_1] :
      ( A_1 = '#skF_9'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246201,c_42])).

tff(c_247052,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_246182,c_246251])).

tff(c_247072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246250,c_247052])).

tff(c_247073,plain,(
    ! [B_5915] : v1_xboole_0(B_5915) ),
    inference(splitRight,[status(thm)],[c_241818])).

tff(c_241728,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_241719])).

tff(c_247140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247073,c_241728])).

tff(c_247141,plain,(
    ! [A_5867] : v1_xboole_0(A_5867) ),
    inference(splitRight,[status(thm)],[c_240848])).

tff(c_247206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247141,c_241728])).

tff(c_247207,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) = k3_zfmisc_1('#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_241333])).

tff(c_240188,plain,(
    ! [A_5803,B_5804,C_5805,D_5806] : r1_tarski(k1_relat_1(k4_zfmisc_1(A_5803,B_5804,C_5805,D_5806)),k3_zfmisc_1(A_5803,B_5804,C_5805)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240169,c_22])).

tff(c_247511,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247207,c_240188])).

tff(c_247639,plain,
    ( k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4')
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(resolution,[status(thm)],[c_247511,c_6])).

tff(c_249174,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_247639])).

tff(c_251599,plain,(
    ! [A_6357,C_6356,A_6361,D_6359,B_6360,B_6358] :
      ( ~ r1_tarski(k2_zfmisc_1(B_6360,A_6357),k4_zfmisc_1(A_6361,B_6358,C_6356,D_6359))
      | r1_tarski(B_6360,k3_zfmisc_1(A_6361,B_6358,C_6356))
      | v1_xboole_0(A_6357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_240386])).

tff(c_251704,plain,(
    ! [B_6362,A_6363] :
      ( ~ r1_tarski(k2_zfmisc_1(B_6362,A_6363),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(B_6362,k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
      | v1_xboole_0(A_6363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239404,c_251599])).

tff(c_253883,plain,(
    ! [A_6445,B_6446,C_6447,D_6448] :
      ( ~ r1_tarski(k4_zfmisc_1(A_6445,B_6446,C_6447,D_6448),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(k3_zfmisc_1(A_6445,B_6446,C_6447),k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
      | v1_xboole_0(D_6448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_251704])).

tff(c_253936,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_253883])).

tff(c_253971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251598,c_249174,c_253936])).

tff(c_253972,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_8') = k3_zfmisc_1('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_247639])).

tff(c_254093,plain,(
    ! [C_6453,D_6456,B_6454,C_6452,A_6455] :
      ( ~ r1_tarski(k3_zfmisc_1(A_6455,B_6454,C_6452),k2_zfmisc_1(C_6453,D_6456))
      | r1_tarski(C_6452,D_6456)
      | v1_xboole_0(k2_zfmisc_1(A_6455,B_6454)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_240271])).

tff(c_254096,plain,(
    ! [C_6453,D_6456] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k2_zfmisc_1(C_6453,D_6456))
      | r1_tarski('#skF_8',D_6456)
      | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253972,c_254093])).

tff(c_255040,plain,(
    ! [C_6485,D_6486] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k2_zfmisc_1(C_6485,D_6486))
      | r1_tarski('#skF_8',D_6486) ) ),
    inference(negUnitSimplification,[status(thm)],[c_241719,c_254096])).

tff(c_255829,plain,(
    ! [A_6517,B_6518,C_6519] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1(A_6517,B_6518,C_6519))
      | r1_tarski('#skF_8',C_6519) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_255040])).

tff(c_255880,plain,(
    r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_255829])).

tff(c_255885,plain,
    ( '#skF_8' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_8') ),
    inference(resolution,[status(thm)],[c_255880,c_6])).

tff(c_255890,plain,(
    ~ r1_tarski('#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_239344,c_255885])).

tff(c_247849,plain,(
    ! [B_6206,A_6207,B_6208,C_6205,A_6209] :
      ( ~ r1_tarski(k2_zfmisc_1(A_6209,B_6208),k3_zfmisc_1(A_6207,B_6206,C_6205))
      | r1_tarski(B_6208,C_6205)
      | v1_xboole_0(A_6209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_240271])).

tff(c_264856,plain,(
    ! [B_6762,A_6763,B_6764,C_6761,A_6766,C_6765] :
      ( ~ r1_tarski(k3_zfmisc_1(A_6766,B_6764,C_6761),k3_zfmisc_1(A_6763,B_6762,C_6765))
      | r1_tarski(C_6761,C_6765)
      | v1_xboole_0(k2_zfmisc_1(A_6766,B_6764)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_247849])).

tff(c_428838,plain,(
    ! [A_8784,B_8785,C_8786] :
      ( ~ r1_tarski(k3_zfmisc_1(A_8784,B_8785,C_8786),k3_zfmisc_1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(C_8786,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1(A_8784,B_8785)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253972,c_264856])).

tff(c_429065,plain,
    ( r1_tarski('#skF_4','#skF_8')
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_428838])).

tff(c_429189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241719,c_255890,c_429065])).

tff(c_429190,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_241578])).

tff(c_429266,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_429190,c_42])).

tff(c_429277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44623,c_429266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 55.92/46.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 56.31/46.16  
% 56.31/46.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 56.31/46.16  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 56.31/46.16  
% 56.31/46.16  %Foreground sorts:
% 56.31/46.16  
% 56.31/46.16  
% 56.31/46.16  %Background operators:
% 56.31/46.16  
% 56.31/46.16  
% 56.31/46.16  %Foreground operators:
% 56.31/46.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.31/46.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 56.31/46.16  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 56.31/46.16  tff('#skF_7', type, '#skF_7': $i).
% 56.31/46.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.31/46.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 56.31/46.16  tff('#skF_5', type, '#skF_5': $i).
% 56.31/46.16  tff('#skF_6', type, '#skF_6': $i).
% 56.31/46.16  tff('#skF_2', type, '#skF_2': $i).
% 56.31/46.16  tff('#skF_3', type, '#skF_3': $i).
% 56.31/46.16  tff('#skF_1', type, '#skF_1': $i).
% 56.31/46.16  tff('#skF_9', type, '#skF_9': $i).
% 56.31/46.16  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 56.31/46.16  tff('#skF_8', type, '#skF_8': $i).
% 56.31/46.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.31/46.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 56.31/46.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 56.31/46.16  tff('#skF_4', type, '#skF_4': $i).
% 56.31/46.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.31/46.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 56.31/46.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 56.31/46.16  
% 56.59/46.22  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 56.59/46.22  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 56.59/46.22  tff(f_80, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 56.59/46.22  tff(f_67, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 56.59/46.22  tff(f_41, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 56.59/46.22  tff(f_65, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 56.59/46.22  tff(f_45, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 56.59/46.22  tff(f_59, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 56.59/46.22  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.59/46.22  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 56.59/46.22  tff(f_63, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 56.59/46.22  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 56.59/46.22  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.59/46.22  tff(c_37, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.59/46.22  tff(c_41, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_37])).
% 56.59/46.22  tff(c_32, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 56.59/46.22  tff(c_48, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_32])).
% 56.59/46.22  tff(c_14111, plain, (![A_975, B_976, C_977, D_978]: (k2_zfmisc_1(k3_zfmisc_1(A_975, B_976, C_977), D_978)=k4_zfmisc_1(A_975, B_976, C_977, D_978))), inference(cnfTransformation, [status(thm)], [f_67])).
% 56.59/46.22  tff(c_13856, plain, (![A_944, B_945]: (v1_xboole_0(k2_zfmisc_1(A_944, B_945)) | ~v1_xboole_0(B_945))), inference(cnfTransformation, [status(thm)], [f_41])).
% 56.59/46.22  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.59/46.22  tff(c_42, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_2])).
% 56.59/46.22  tff(c_13867, plain, (![A_946, B_947]: (k2_zfmisc_1(A_946, B_947)='#skF_1' | ~v1_xboole_0(B_947))), inference(resolution, [status(thm)], [c_13856, c_42])).
% 56.59/46.22  tff(c_13876, plain, (![A_946]: (k2_zfmisc_1(A_946, '#skF_1')='#skF_1')), inference(resolution, [status(thm)], [c_4, c_13867])).
% 56.59/46.22  tff(c_14121, plain, (![A_975, B_976, C_977]: (k4_zfmisc_1(A_975, B_976, C_977, '#skF_1')='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14111, c_13876])).
% 56.59/46.22  tff(c_1231, plain, (![A_381, B_382, C_383, D_384]: (k2_zfmisc_1(k3_zfmisc_1(A_381, B_382, C_383), D_384)=k4_zfmisc_1(A_381, B_382, C_383, D_384))), inference(cnfTransformation, [status(thm)], [f_67])).
% 56.59/46.22  tff(c_62, plain, (![A_36, B_37]: (v1_xboole_0(k2_zfmisc_1(A_36, B_37)) | ~v1_xboole_0(B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 56.59/46.22  tff(c_111, plain, (![A_43, B_44]: (k2_zfmisc_1(A_43, B_44)='#skF_1' | ~v1_xboole_0(B_44))), inference(resolution, [status(thm)], [c_62, c_42])).
% 56.59/46.22  tff(c_120, plain, (![A_43]: (k2_zfmisc_1(A_43, '#skF_1')='#skF_1')), inference(resolution, [status(thm)], [c_4, c_111])).
% 56.59/46.22  tff(c_1248, plain, (![A_381, B_382, C_383]: (k4_zfmisc_1(A_381, B_382, C_383, '#skF_1')='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_120])).
% 56.59/46.22  tff(c_12, plain, (![A_4, B_5]: (v1_xboole_0(k2_zfmisc_1(A_4, B_5)) | ~v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 56.59/46.22  tff(c_1118, plain, (![A_369, B_370, C_371]: (k2_zfmisc_1(k2_zfmisc_1(A_369, B_370), C_371)=k3_zfmisc_1(A_369, B_370, C_371))), inference(cnfTransformation, [status(thm)], [f_65])).
% 56.59/46.22  tff(c_14, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.59/46.22  tff(c_1141, plain, (![A_369, B_370, C_371]: (v1_xboole_0(k3_zfmisc_1(A_369, B_370, C_371)) | ~v1_xboole_0(k2_zfmisc_1(A_369, B_370)))), inference(superposition, [status(thm), theory('equality')], [c_1118, c_14])).
% 56.59/46.22  tff(c_34, plain, (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 56.59/46.22  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_17, B_18)), A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 56.59/46.22  tff(c_2717, plain, (![A_485, B_486, C_487, D_488]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_485, B_486, C_487, D_488)), k3_zfmisc_1(A_485, B_486, C_487)))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_22])).
% 56.59/46.22  tff(c_2761, plain, (r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2717])).
% 56.59/46.22  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.59/46.22  tff(c_2847, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_2761, c_6])).
% 56.59/46.22  tff(c_3179, plain, (~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_2847])).
% 56.59/46.22  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.59/46.22  tff(c_1259, plain, (![A_381, B_382, C_383, D_384]: (v1_relat_1(k4_zfmisc_1(A_381, B_382, C_383, D_384)))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_20])).
% 56.59/46.22  tff(c_24, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 56.59/46.22  tff(c_1517, plain, (![A_415, B_416, C_417, D_418]: (v1_xboole_0(k4_zfmisc_1(A_415, B_416, C_417, D_418)) | ~v1_xboole_0(D_418))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_12])).
% 56.59/46.22  tff(c_1541, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1517])).
% 56.59/46.22  tff(c_1615, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1541])).
% 56.59/46.22  tff(c_28, plain, (![A_23, B_24, C_25, D_26]: (k2_zfmisc_1(k3_zfmisc_1(A_23, B_24, C_25), D_26)=k4_zfmisc_1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 56.59/46.22  tff(c_1300, plain, (![B_392, A_393, D_394, C_395]: (~r1_tarski(k2_zfmisc_1(B_392, A_393), k2_zfmisc_1(D_394, C_395)) | r1_tarski(B_392, D_394) | v1_xboole_0(A_393))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_7022, plain, (![C_674, C_670, D_669, D_672, B_671, A_673]: (~r1_tarski(k4_zfmisc_1(A_673, B_671, C_670, D_672), k2_zfmisc_1(D_669, C_674)) | r1_tarski(k3_zfmisc_1(A_673, B_671, C_670), D_669) | v1_xboole_0(D_672))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1300])).
% 56.59/46.22  tff(c_7048, plain, (![D_669, C_674]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_669, C_674)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), D_669) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_7022])).
% 56.59/46.22  tff(c_7058, plain, (![D_675, C_676]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_675, C_676)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), D_675))), inference(negUnitSimplification, [status(thm)], [c_1615, c_7048])).
% 56.59/46.22  tff(c_7080, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_7058])).
% 56.59/46.22  tff(c_7085, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1259, c_7080])).
% 56.59/46.22  tff(c_7087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3179, c_7085])).
% 56.59/46.22  tff(c_7088, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_2847])).
% 56.59/46.22  tff(c_1257, plain, (![A_381, B_382, C_383, D_384]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_381, B_382, C_383, D_384)), k3_zfmisc_1(A_381, B_382, C_383)))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_22])).
% 56.59/46.22  tff(c_7304, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7088, c_1257])).
% 56.59/46.22  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.59/46.22  tff(c_56, plain, (![A_34, B_35]: (v1_xboole_0(k2_zfmisc_1(A_34, B_35)) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.59/46.22  tff(c_67, plain, (![A_38, B_39]: (k2_zfmisc_1(A_38, B_39)='#skF_1' | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_56, c_42])).
% 56.59/46.22  tff(c_77, plain, (![B_40]: (k2_zfmisc_1('#skF_1', B_40)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_67])).
% 56.59/46.22  tff(c_88, plain, (r1_tarski(k1_relat_1('#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_77, c_22])).
% 56.59/46.22  tff(c_110, plain, (k1_relat_1('#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_6])).
% 56.59/46.22  tff(c_160, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_110])).
% 56.59/46.22  tff(c_76, plain, (![B_39]: (k2_zfmisc_1('#skF_1', B_39)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_67])).
% 56.59/46.22  tff(c_586, plain, (![B_82, A_83, D_84, C_85]: (~r1_tarski(k2_zfmisc_1(B_82, A_83), k2_zfmisc_1(D_84, C_85)) | r1_tarski(B_82, D_84) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_608, plain, (![B_82, A_83]: (r1_tarski(B_82, k1_relat_1(k2_zfmisc_1(B_82, A_83))) | v1_xboole_0(A_83) | ~v1_relat_1(k2_zfmisc_1(B_82, A_83)))), inference(resolution, [status(thm)], [c_24, c_586])).
% 56.59/46.22  tff(c_821, plain, (![B_111, A_112]: (r1_tarski(B_111, k1_relat_1(k2_zfmisc_1(B_111, A_112))) | v1_xboole_0(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_608])).
% 56.59/46.22  tff(c_841, plain, (![B_39]: (r1_tarski('#skF_1', k1_relat_1('#skF_1')) | v1_xboole_0(B_39))), inference(superposition, [status(thm), theory('equality')], [c_76, c_821])).
% 56.59/46.22  tff(c_847, plain, (![B_39]: (v1_xboole_0(B_39))), inference(negUnitSimplification, [status(thm)], [c_160, c_841])).
% 56.59/46.22  tff(c_915, plain, (![A_118]: (A_118='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_42])).
% 56.59/46.22  tff(c_970, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_915, c_160])).
% 56.59/46.22  tff(c_1027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_970])).
% 56.59/46.22  tff(c_1028, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_110])).
% 56.59/46.22  tff(c_121, plain, (![A_45]: (k2_zfmisc_1(A_45, '#skF_1')='#skF_1')), inference(resolution, [status(thm)], [c_4, c_111])).
% 56.59/46.22  tff(c_135, plain, (![A_45]: (r1_tarski(k1_relat_1('#skF_1'), A_45))), inference(superposition, [status(thm), theory('equality')], [c_121, c_22])).
% 56.59/46.22  tff(c_1030, plain, (![A_45]: (r1_tarski('#skF_1', A_45))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_135])).
% 56.59/46.22  tff(c_1740, plain, (![A_442, A_443, B_444]: (k2_zfmisc_1(A_442, k2_zfmisc_1(A_443, B_444))='#skF_1' | ~v1_xboole_0(A_443))), inference(resolution, [status(thm)], [c_14, c_111])).
% 56.59/46.22  tff(c_18, plain, (![A_8, B_12, C_13, D_14]: (~r1_tarski(k2_zfmisc_1(A_8, B_12), k2_zfmisc_1(C_13, D_14)) | r1_tarski(B_12, D_14) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_1761, plain, (![A_443, D_14, B_444, A_442, C_13]: (~r1_tarski('#skF_1', k2_zfmisc_1(C_13, D_14)) | r1_tarski(k2_zfmisc_1(A_443, B_444), D_14) | v1_xboole_0(A_442) | ~v1_xboole_0(A_443))), inference(superposition, [status(thm), theory('equality')], [c_1740, c_18])).
% 56.59/46.22  tff(c_1842, plain, (![A_443, B_444, D_14, A_442]: (r1_tarski(k2_zfmisc_1(A_443, B_444), D_14) | v1_xboole_0(A_442) | ~v1_xboole_0(A_443))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_1761])).
% 56.59/46.22  tff(c_2770, plain, (![A_489, B_490, D_491]: (r1_tarski(k2_zfmisc_1(A_489, B_490), D_491) | ~v1_xboole_0(A_489))), inference(splitLeft, [status(thm)], [c_1842])).
% 56.59/46.22  tff(c_16, plain, (![B_12, A_8, D_14, C_13]: (~r1_tarski(k2_zfmisc_1(B_12, A_8), k2_zfmisc_1(D_14, C_13)) | r1_tarski(B_12, D_14) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_2813, plain, (![A_489, D_14, B_490]: (r1_tarski(A_489, D_14) | v1_xboole_0(B_490) | ~v1_xboole_0(A_489))), inference(resolution, [status(thm)], [c_2770, c_16])).
% 56.59/46.22  tff(c_2823, plain, (![A_492, D_493]: (r1_tarski(A_492, D_493) | ~v1_xboole_0(A_492))), inference(splitLeft, [status(thm)], [c_2813])).
% 56.59/46.22  tff(c_2844, plain, (![D_493, A_492]: (D_493=A_492 | ~r1_tarski(D_493, A_492) | ~v1_xboole_0(A_492))), inference(resolution, [status(thm)], [c_2823, c_6])).
% 56.59/46.22  tff(c_7318, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_7304, c_2844])).
% 56.59/46.22  tff(c_8674, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7318])).
% 56.59/46.22  tff(c_8681, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1141, c_8674])).
% 56.59/46.22  tff(c_8689, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_8681])).
% 56.59/46.22  tff(c_30, plain, ('#skF_5'!='#skF_9' | '#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 56.59/46.22  tff(c_61, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 56.59/46.22  tff(c_2536, plain, (![A_477, B_478, C_479, D_480]: (v1_xboole_0(k4_zfmisc_1(A_477, B_478, C_479, D_480)) | ~v1_xboole_0(k3_zfmisc_1(A_477, B_478, C_479)))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_14])).
% 56.59/46.22  tff(c_2568, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2536])).
% 56.59/46.22  tff(c_2700, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2568])).
% 56.59/46.22  tff(c_2707, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1141, c_2700])).
% 56.59/46.22  tff(c_2715, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12, c_2707])).
% 56.59/46.22  tff(c_1138, plain, (![A_369, B_370, C_371]: (v1_xboole_0(k3_zfmisc_1(A_369, B_370, C_371)) | ~v1_xboole_0(C_371))), inference(superposition, [status(thm), theory('equality')], [c_1118, c_12])).
% 56.59/46.22  tff(c_8682, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1138, c_8674])).
% 56.59/46.22  tff(c_2708, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1138, c_2700])).
% 56.59/46.22  tff(c_118, plain, (![A_43, A_4, B_5]: (k2_zfmisc_1(A_43, k2_zfmisc_1(A_4, B_5))='#skF_1' | ~v1_xboole_0(B_5))), inference(resolution, [status(thm)], [c_12, c_111])).
% 56.59/46.22  tff(c_1467, plain, (![A_411, B_412, C_413, D_414]: (~r1_tarski(k2_zfmisc_1(A_411, B_412), k2_zfmisc_1(C_413, D_414)) | r1_tarski(B_412, D_414) | v1_xboole_0(A_411))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_1482, plain, (![B_5, C_413, A_4, D_414, A_43]: (~r1_tarski('#skF_1', k2_zfmisc_1(C_413, D_414)) | r1_tarski(k2_zfmisc_1(A_4, B_5), D_414) | v1_xboole_0(A_43) | ~v1_xboole_0(B_5))), inference(superposition, [status(thm), theory('equality')], [c_118, c_1467])).
% 56.59/46.22  tff(c_1507, plain, (![A_4, B_5, D_414, A_43]: (r1_tarski(k2_zfmisc_1(A_4, B_5), D_414) | v1_xboole_0(A_43) | ~v1_xboole_0(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_1482])).
% 56.59/46.22  tff(c_7091, plain, (![A_677, B_678, D_679]: (r1_tarski(k2_zfmisc_1(A_677, B_678), D_679) | ~v1_xboole_0(B_678))), inference(splitLeft, [status(thm)], [c_1507])).
% 56.59/46.22  tff(c_7121, plain, (![A_23, B_24, D_26, C_25, D_679]: (r1_tarski(k4_zfmisc_1(A_23, B_24, C_25, D_26), D_679) | ~v1_xboole_0(D_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7091])).
% 56.59/46.22  tff(c_10510, plain, (![D_827, A_831, B_829, C_828, D_830, C_832]: (~r1_tarski(k4_zfmisc_1(A_831, B_829, C_828, D_830), k2_zfmisc_1(D_827, C_832)) | r1_tarski(k3_zfmisc_1(A_831, B_829, C_828), D_827) | v1_xboole_0(D_830))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1300])).
% 56.59/46.22  tff(c_10584, plain, (![D_827, C_832]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_827, C_832)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), D_827) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10510])).
% 56.59/46.22  tff(c_10621, plain, (![D_833, C_834]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_833, C_834)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), D_833))), inference(negUnitSimplification, [status(thm)], [c_1615, c_10584])).
% 56.59/46.22  tff(c_10662, plain, (![D_833]: (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), D_833) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_7121, c_10621])).
% 56.59/46.22  tff(c_10667, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_10662])).
% 56.59/46.22  tff(c_10854, plain, (![B_844, B_846, D_845, A_847, A_848, C_843]: (~r1_tarski(k2_zfmisc_1(B_846, A_848), k4_zfmisc_1(A_847, B_844, C_843, D_845)) | r1_tarski(B_846, k3_zfmisc_1(A_847, B_844, C_843)) | v1_xboole_0(A_848))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1300])).
% 56.59/46.22  tff(c_10959, plain, (![B_849, A_850]: (~r1_tarski(k2_zfmisc_1(B_849, A_850), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(B_849, k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0(A_850))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10854])).
% 56.59/46.22  tff(c_12327, plain, (![A_909, B_910, C_911, D_912]: (~r1_tarski(k4_zfmisc_1(A_909, B_910, C_911, D_912), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(k3_zfmisc_1(A_909, B_910, C_911), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0(D_912))), inference(superposition, [status(thm), theory('equality')], [c_28, c_10959])).
% 56.59/46.22  tff(c_12377, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_10, c_12327])).
% 56.59/46.22  tff(c_12409, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_10667, c_12377])).
% 56.59/46.22  tff(c_12727, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_12409, c_6])).
% 56.59/46.22  tff(c_12731, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7304, c_12727])).
% 56.59/46.22  tff(c_26, plain, (![A_20, B_21, C_22]: (k2_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22)=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 56.59/46.22  tff(c_1322, plain, (![B_392, A_393]: (r1_tarski(B_392, k1_relat_1(k2_zfmisc_1(B_392, A_393))) | v1_xboole_0(A_393) | ~v1_relat_1(k2_zfmisc_1(B_392, A_393)))), inference(resolution, [status(thm)], [c_24, c_1300])).
% 56.59/46.22  tff(c_1551, plain, (![B_419, A_420]: (r1_tarski(B_419, k1_relat_1(k2_zfmisc_1(B_419, A_420))) | v1_xboole_0(A_420))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1322])).
% 56.59/46.22  tff(c_1553, plain, (![B_419, A_420]: (k1_relat_1(k2_zfmisc_1(B_419, A_420))=B_419 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(B_419, A_420)), B_419) | v1_xboole_0(A_420))), inference(resolution, [status(thm)], [c_1551, c_6])).
% 56.59/46.22  tff(c_1575, plain, (![B_421, A_422]: (k1_relat_1(k2_zfmisc_1(B_421, A_422))=B_421 | v1_xboole_0(A_422))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1553])).
% 56.59/46.22  tff(c_1596, plain, (![A_20, B_21, C_22]: (k1_relat_1(k3_zfmisc_1(A_20, B_21, C_22))=k2_zfmisc_1(A_20, B_21) | v1_xboole_0(C_22))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1575])).
% 56.59/46.22  tff(c_12792, plain, (k1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_6', '#skF_7') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_12731, c_1596])).
% 56.59/46.22  tff(c_12828, plain, (k1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2708, c_12792])).
% 56.59/46.22  tff(c_12856, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12828, c_1596])).
% 56.59/46.22  tff(c_12877, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_8682, c_12856])).
% 56.59/46.22  tff(c_1571, plain, (![B_419, A_420]: (k1_relat_1(k2_zfmisc_1(B_419, A_420))=B_419 | v1_xboole_0(A_420))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1553])).
% 56.59/46.22  tff(c_12995, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_6' | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12877, c_1571])).
% 56.59/46.22  tff(c_13042, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_2715, c_12995])).
% 56.59/46.22  tff(c_13063, plain, ('#skF_6'='#skF_2' | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13042, c_1571])).
% 56.59/46.22  tff(c_13087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8689, c_61, c_13063])).
% 56.59/46.22  tff(c_13089, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_10662])).
% 56.59/46.22  tff(c_13132, plain, ('#skF_5'='#skF_1'), inference(resolution, [status(thm)], [c_13089, c_42])).
% 56.59/46.22  tff(c_13143, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13132, c_48])).
% 56.59/46.22  tff(c_13155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1248, c_13143])).
% 56.59/46.22  tff(c_13157, plain, (v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_7318])).
% 56.59/46.22  tff(c_13200, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_13157, c_42])).
% 56.59/46.22  tff(c_13202, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13200, c_7304])).
% 56.59/46.22  tff(c_1035, plain, (![A_363]: (r1_tarski('#skF_1', A_363))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_135])).
% 56.59/46.22  tff(c_1038, plain, (![A_363]: (A_363='#skF_1' | ~r1_tarski(A_363, '#skF_1'))), inference(resolution, [status(thm)], [c_1035, c_6])).
% 56.59/46.22  tff(c_13264, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')='#skF_1'), inference(resolution, [status(thm)], [c_13202, c_1038])).
% 56.59/46.22  tff(c_13270, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13264, c_2700])).
% 56.59/46.22  tff(c_13274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_13270])).
% 56.59/46.22  tff(c_13275, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2568])).
% 56.59/46.22  tff(c_13403, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_13275, c_42])).
% 56.59/46.22  tff(c_13414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_13403])).
% 56.59/46.22  tff(c_13416, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1541])).
% 56.59/46.22  tff(c_13429, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_13416, c_42])).
% 56.59/46.22  tff(c_13448, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_13429, c_48])).
% 56.59/46.22  tff(c_13434, plain, (![A_381, B_382, C_383]: (k4_zfmisc_1(A_381, B_382, C_383, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13429, c_13429, c_1248])).
% 56.59/46.22  tff(c_13847, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_13434, c_34])).
% 56.59/46.22  tff(c_13849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13448, c_13847])).
% 56.59/46.22  tff(c_13850, plain, ('#skF_7'!='#skF_3' | '#skF_8'!='#skF_4' | '#skF_5'!='#skF_9'), inference(splitRight, [status(thm)], [c_30])).
% 56.59/46.22  tff(c_13866, plain, ('#skF_5'!='#skF_9'), inference(splitLeft, [status(thm)], [c_13850])).
% 56.59/46.22  tff(c_13851, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 56.59/46.22  tff(c_13861, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13851, c_34])).
% 56.59/46.22  tff(c_15166, plain, (![A_1057, B_1058, C_1059, D_1060]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_1057, B_1058, C_1059, D_1060)), k3_zfmisc_1(A_1057, B_1058, C_1059)))), inference(superposition, [status(thm), theory('equality')], [c_14111, c_22])).
% 56.59/46.22  tff(c_15198, plain, (r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_15166])).
% 56.59/46.22  tff(c_15405, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_15198, c_6])).
% 56.59/46.22  tff(c_15797, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_15405])).
% 56.59/46.22  tff(c_14132, plain, (![A_975, B_976, C_977, D_978]: (v1_relat_1(k4_zfmisc_1(A_975, B_976, C_977, D_978)))), inference(superposition, [status(thm), theory('equality')], [c_14111, c_20])).
% 56.59/46.22  tff(c_14306, plain, (![A_1000, B_1001, C_1002, D_1003]: (v1_xboole_0(k4_zfmisc_1(A_1000, B_1001, C_1002, D_1003)) | ~v1_xboole_0(D_1003))), inference(superposition, [status(thm), theory('equality')], [c_14111, c_12])).
% 56.59/46.22  tff(c_14330, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_13861, c_14306])).
% 56.59/46.22  tff(c_14340, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_14330])).
% 56.59/46.22  tff(c_14213, plain, (![B_992, A_993, D_994, C_995]: (~r1_tarski(k2_zfmisc_1(B_992, A_993), k2_zfmisc_1(D_994, C_995)) | r1_tarski(B_992, D_994) | v1_xboole_0(A_993))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_20183, plain, (![D_1284, C_1283, A_1288, B_1285, D_1286, C_1287]: (~r1_tarski(k4_zfmisc_1(A_1288, B_1285, C_1283, D_1286), k2_zfmisc_1(D_1284, C_1287)) | r1_tarski(k3_zfmisc_1(A_1288, B_1285, C_1283), D_1284) | v1_xboole_0(D_1286))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14213])).
% 56.59/46.22  tff(c_20263, plain, (![D_1284, C_1287]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_1284, C_1287)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_1284) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_20183])).
% 56.59/46.22  tff(c_20294, plain, (![D_1289, C_1290]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_1289, C_1290)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_1289))), inference(negUnitSimplification, [status(thm)], [c_14340, c_20263])).
% 56.59/46.22  tff(c_20325, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_20294])).
% 56.59/46.22  tff(c_20339, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14132, c_20325])).
% 56.59/46.22  tff(c_20341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15797, c_20339])).
% 56.59/46.22  tff(c_20342, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_15405])).
% 56.59/46.22  tff(c_14130, plain, (![A_975, B_976, C_977, D_978]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_975, B_976, C_977, D_978)), k3_zfmisc_1(A_975, B_976, C_977)))), inference(superposition, [status(thm), theory('equality')], [c_14111, c_22])).
% 56.59/46.22  tff(c_20683, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_20342, c_14130])).
% 56.59/46.22  tff(c_13877, plain, (![A_948]: (k2_zfmisc_1(A_948, '#skF_1')='#skF_1')), inference(resolution, [status(thm)], [c_4, c_13867])).
% 56.59/46.22  tff(c_13888, plain, (![A_948]: (r1_tarski(k1_relat_1('#skF_1'), A_948))), inference(superposition, [status(thm), theory('equality')], [c_13877, c_22])).
% 56.59/46.22  tff(c_13912, plain, (![A_952, B_953]: (k2_zfmisc_1(A_952, B_953)='#skF_1' | ~v1_xboole_0(A_952))), inference(resolution, [status(thm)], [c_56, c_42])).
% 56.59/46.22  tff(c_13921, plain, (![B_953]: (k2_zfmisc_1('#skF_1', B_953)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_13912])).
% 56.59/46.22  tff(c_14223, plain, (![B_992, A_993]: (r1_tarski(B_992, k1_relat_1(k2_zfmisc_1(B_992, A_993))) | v1_xboole_0(A_993) | ~v1_relat_1(k2_zfmisc_1(B_992, A_993)))), inference(resolution, [status(thm)], [c_24, c_14213])).
% 56.59/46.22  tff(c_14341, plain, (![B_1004, A_1005]: (r1_tarski(B_1004, k1_relat_1(k2_zfmisc_1(B_1004, A_1005))) | v1_xboole_0(A_1005))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14223])).
% 56.59/46.22  tff(c_14355, plain, (![B_953]: (r1_tarski('#skF_1', k1_relat_1('#skF_1')) | v1_xboole_0(B_953))), inference(superposition, [status(thm), theory('equality')], [c_13921, c_14341])).
% 56.59/46.22  tff(c_14364, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_14355])).
% 56.59/46.22  tff(c_14369, plain, (k1_relat_1('#skF_1')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_14364, c_6])).
% 56.59/46.22  tff(c_14373, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13888, c_14369])).
% 56.59/46.22  tff(c_14377, plain, (![A_948]: (r1_tarski('#skF_1', A_948))), inference(demodulation, [status(thm), theory('equality')], [c_14373, c_13888])).
% 56.59/46.22  tff(c_14625, plain, (![A_1023, A_1024, B_1025]: (k2_zfmisc_1(A_1023, k2_zfmisc_1(A_1024, B_1025))='#skF_1' | ~v1_xboole_0(A_1024))), inference(resolution, [status(thm)], [c_14, c_13867])).
% 56.59/46.22  tff(c_14646, plain, (![A_1024, D_14, B_1025, C_13, A_1023]: (~r1_tarski('#skF_1', k2_zfmisc_1(C_13, D_14)) | r1_tarski(k2_zfmisc_1(A_1024, B_1025), D_14) | v1_xboole_0(A_1023) | ~v1_xboole_0(A_1024))), inference(superposition, [status(thm), theory('equality')], [c_14625, c_18])).
% 56.59/46.22  tff(c_14725, plain, (![A_1024, B_1025, D_14, A_1023]: (r1_tarski(k2_zfmisc_1(A_1024, B_1025), D_14) | v1_xboole_0(A_1023) | ~v1_xboole_0(A_1024))), inference(demodulation, [status(thm), theory('equality')], [c_14377, c_14646])).
% 56.59/46.22  tff(c_15745, plain, (![A_1083, B_1084, D_1085]: (r1_tarski(k2_zfmisc_1(A_1083, B_1084), D_1085) | ~v1_xboole_0(A_1083))), inference(splitLeft, [status(thm)], [c_14725])).
% 56.59/46.22  tff(c_15789, plain, (![A_1083, D_14, B_1084]: (r1_tarski(A_1083, D_14) | v1_xboole_0(B_1084) | ~v1_xboole_0(A_1083))), inference(resolution, [status(thm)], [c_15745, c_16])).
% 56.59/46.22  tff(c_20345, plain, (![A_1291, D_1292]: (r1_tarski(A_1291, D_1292) | ~v1_xboole_0(A_1291))), inference(splitLeft, [status(thm)], [c_15789])).
% 56.59/46.22  tff(c_20366, plain, (![D_1292, A_1291]: (D_1292=A_1291 | ~r1_tarski(D_1292, A_1291) | ~v1_xboole_0(A_1291))), inference(resolution, [status(thm)], [c_20345, c_6])).
% 56.59/46.22  tff(c_20719, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20683, c_20366])).
% 56.59/46.22  tff(c_21270, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_20719])).
% 56.59/46.22  tff(c_14389, plain, (![A_1006, B_1007, C_1008, D_1009]: (~r1_tarski(k2_zfmisc_1(A_1006, B_1007), k2_zfmisc_1(C_1008, D_1009)) | r1_tarski(B_1007, D_1009) | v1_xboole_0(A_1006))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_22226, plain, (![C_1394, A_1399, B_1396, D_1398, B_1397, A_1395]: (~r1_tarski(k2_zfmisc_1(A_1395, B_1396), k4_zfmisc_1(A_1399, B_1397, C_1394, D_1398)) | r1_tarski(B_1396, D_1398) | v1_xboole_0(A_1395))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14389])).
% 56.59/46.22  tff(c_22309, plain, (![A_1400, B_1401]: (~r1_tarski(k2_zfmisc_1(A_1400, B_1401), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(B_1401, '#skF_9') | v1_xboole_0(A_1400))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_22226])).
% 56.59/46.22  tff(c_23358, plain, (![A_1438, B_1439, C_1440, D_1441]: (~r1_tarski(k4_zfmisc_1(A_1438, B_1439, C_1440, D_1441), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(D_1441, '#skF_9') | v1_xboole_0(k3_zfmisc_1(A_1438, B_1439, C_1440)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_22309])).
% 56.59/46.22  tff(c_23402, plain, (r1_tarski('#skF_5', '#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_23358])).
% 56.59/46.22  tff(c_23430, plain, (r1_tarski('#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_21270, c_23402])).
% 56.59/46.22  tff(c_23435, plain, ('#skF_5'='#skF_9' | ~r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_23430, c_6])).
% 56.59/46.22  tff(c_23440, plain, (~r1_tarski('#skF_9', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_13866, c_23435])).
% 56.59/46.22  tff(c_14523, plain, (![A_1020, A_1021, B_1022]: (k2_zfmisc_1(A_1020, k2_zfmisc_1(A_1021, B_1022))='#skF_1' | ~v1_xboole_0(B_1022))), inference(resolution, [status(thm)], [c_12, c_13867])).
% 56.59/46.22  tff(c_14538, plain, (![A_1020, B_1022, A_1021, D_14, C_13]: (~r1_tarski('#skF_1', k2_zfmisc_1(C_13, D_14)) | r1_tarski(k2_zfmisc_1(A_1021, B_1022), D_14) | v1_xboole_0(A_1020) | ~v1_xboole_0(B_1022))), inference(superposition, [status(thm), theory('equality')], [c_14523, c_18])).
% 56.59/46.22  tff(c_14609, plain, (![A_1021, B_1022, D_14, A_1020]: (r1_tarski(k2_zfmisc_1(A_1021, B_1022), D_14) | v1_xboole_0(A_1020) | ~v1_xboole_0(B_1022))), inference(demodulation, [status(thm), theory('equality')], [c_14377, c_14538])).
% 56.59/46.22  tff(c_20722, plain, (![A_1317, B_1318, D_1319]: (r1_tarski(k2_zfmisc_1(A_1317, B_1318), D_1319) | ~v1_xboole_0(B_1318))), inference(splitLeft, [status(thm)], [c_14609])).
% 56.59/46.22  tff(c_20755, plain, (![D_1319, A_23, B_24, D_26, C_25]: (r1_tarski(k4_zfmisc_1(A_23, B_24, C_25, D_26), D_1319) | ~v1_xboole_0(D_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_20722])).
% 56.59/46.22  tff(c_24071, plain, (![D_1466, C_1469, A_1470, D_1468, B_1467, C_1465]: (~r1_tarski(k4_zfmisc_1(A_1470, B_1467, C_1465, D_1468), k2_zfmisc_1(D_1466, C_1469)) | r1_tarski(k3_zfmisc_1(A_1470, B_1467, C_1465), D_1466) | v1_xboole_0(D_1468))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14213])).
% 56.59/46.22  tff(c_24151, plain, (![D_1466, C_1469]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_1466, C_1469)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_1466) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_24071])).
% 56.59/46.22  tff(c_24182, plain, (![D_1471, C_1472]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(D_1471, C_1472)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_1471))), inference(negUnitSimplification, [status(thm)], [c_14340, c_24151])).
% 56.59/46.22  tff(c_24223, plain, (![D_1471]: (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_1471) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_20755, c_24182])).
% 56.59/46.22  tff(c_24228, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_24223])).
% 56.59/46.22  tff(c_24492, plain, (![A_1489, A_1488, B_1485, B_1486, C_1484, D_1487]: (~r1_tarski(k2_zfmisc_1(B_1486, A_1488), k4_zfmisc_1(A_1489, B_1485, C_1484, D_1487)) | r1_tarski(B_1486, k3_zfmisc_1(A_1489, B_1485, C_1484)) | v1_xboole_0(A_1488))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14213])).
% 56.59/46.22  tff(c_24978, plain, (![B_1499, A_1500]: (~r1_tarski(k2_zfmisc_1(B_1499, A_1500), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(B_1499, k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(A_1500))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_24492])).
% 56.59/46.22  tff(c_26428, plain, (![A_1557, B_1558, C_1559, D_1560]: (~r1_tarski(k4_zfmisc_1(A_1557, B_1558, C_1559, D_1560), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(k3_zfmisc_1(A_1557, B_1558, C_1559), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(D_1560))), inference(superposition, [status(thm), theory('equality')], [c_28, c_24978])).
% 56.59/46.22  tff(c_26478, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_10, c_26428])).
% 56.59/46.22  tff(c_26510, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_24228, c_26478])).
% 56.59/46.22  tff(c_26515, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_26510, c_6])).
% 56.59/46.22  tff(c_26519, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20683, c_26515])).
% 56.59/46.22  tff(c_26601, plain, (![D_26]: (k2_zfmisc_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), D_26)=k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', D_26))), inference(superposition, [status(thm), theory('equality')], [c_26519, c_28])).
% 56.59/46.22  tff(c_26618, plain, (![D_26]: (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', D_26)=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', D_26))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26601])).
% 56.59/46.22  tff(c_31156, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26618, c_13861])).
% 56.59/46.22  tff(c_15406, plain, (![A_1069, B_1070, C_1071, D_1072]: (v1_xboole_0(k4_zfmisc_1(A_1069, B_1070, C_1071, D_1072)) | ~v1_xboole_0(k3_zfmisc_1(A_1069, B_1070, C_1071)))), inference(superposition, [status(thm), theory('equality')], [c_14111, c_14])).
% 56.59/46.22  tff(c_15438, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_15406])).
% 56.59/46.22  tff(c_15564, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_15438])).
% 56.59/46.22  tff(c_24230, plain, (![D_1477, D_1474, C_1475, A_1478, C_1473, B_1476]: (~r1_tarski(k4_zfmisc_1(A_1478, B_1476, C_1473, D_1477), k2_zfmisc_1(C_1475, D_1474)) | r1_tarski(D_1477, D_1474) | v1_xboole_0(k3_zfmisc_1(A_1478, B_1476, C_1473)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14389])).
% 56.59/46.22  tff(c_24310, plain, (![C_1475, D_1474]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(C_1475, D_1474)) | r1_tarski('#skF_9', D_1474) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_13861, c_24230])).
% 56.59/46.22  tff(c_24417, plain, (![C_1482, D_1483]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(C_1482, D_1483)) | r1_tarski('#skF_9', D_1483))), inference(negUnitSimplification, [status(thm)], [c_15564, c_24310])).
% 56.59/46.22  tff(c_24444, plain, (![A_23, B_24, C_25, D_26]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k4_zfmisc_1(A_23, B_24, C_25, D_26)) | r1_tarski('#skF_9', D_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_24417])).
% 56.59/46.22  tff(c_43716, plain, (![A_1898, B_1899, C_1900, D_1901]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1898, B_1899, C_1900, D_1901)) | r1_tarski('#skF_9', D_1901))), inference(demodulation, [status(thm), theory('equality')], [c_31156, c_24444])).
% 56.59/46.22  tff(c_43749, plain, (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski('#skF_9', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_31156, c_43716])).
% 56.59/46.22  tff(c_43800, plain, (r1_tarski('#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_43749])).
% 56.59/46.22  tff(c_43802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23440, c_43800])).
% 56.59/46.22  tff(c_43804, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_24223])).
% 56.59/46.22  tff(c_43847, plain, ('#skF_5'='#skF_1'), inference(resolution, [status(thm)], [c_43804, c_42])).
% 56.59/46.22  tff(c_43859, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_43847, c_48])).
% 56.59/46.22  tff(c_43872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14121, c_43859])).
% 56.59/46.22  tff(c_43874, plain, (v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_20719])).
% 56.59/46.22  tff(c_43917, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_43874, c_42])).
% 56.59/46.22  tff(c_43919, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43917, c_20683])).
% 56.59/46.22  tff(c_43964, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')='#skF_1' | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_43919, c_20366])).
% 56.59/46.22  tff(c_43972, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_43964])).
% 56.59/46.22  tff(c_44117, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43972, c_15564])).
% 56.59/46.22  tff(c_44121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_44117])).
% 56.59/46.22  tff(c_44122, plain, (![B_1084]: (v1_xboole_0(B_1084))), inference(splitRight, [status(thm)], [c_15789])).
% 56.59/46.22  tff(c_13953, plain, (![A_955, B_956, C_957]: (k2_zfmisc_1(k2_zfmisc_1(A_955, B_956), C_957)=k3_zfmisc_1(A_955, B_956, C_957))), inference(cnfTransformation, [status(thm)], [f_65])).
% 56.59/46.22  tff(c_13969, plain, (![A_955, B_956, C_957]: (v1_xboole_0(k3_zfmisc_1(A_955, B_956, C_957)) | ~v1_xboole_0(k2_zfmisc_1(A_955, B_956)))), inference(superposition, [status(thm), theory('equality')], [c_13953, c_14])).
% 56.59/46.22  tff(c_15571, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_7'))), inference(resolution, [status(thm)], [c_13969, c_15564])).
% 56.59/46.22  tff(c_15580, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_15571])).
% 56.59/46.22  tff(c_44191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44122, c_15580])).
% 56.59/46.22  tff(c_44192, plain, (![A_1023]: (v1_xboole_0(A_1023))), inference(splitRight, [status(thm)], [c_14725])).
% 56.59/46.22  tff(c_44259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44192, c_15580])).
% 56.59/46.22  tff(c_44260, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_15438])).
% 56.59/46.22  tff(c_44336, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_44260, c_42])).
% 56.59/46.22  tff(c_44347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_44336])).
% 56.59/46.22  tff(c_44348, plain, (![B_953]: (v1_xboole_0(B_953))), inference(splitRight, [status(thm)], [c_14355])).
% 56.59/46.22  tff(c_44371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44348, c_14340])).
% 56.59/46.22  tff(c_44373, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_14330])).
% 56.59/46.22  tff(c_44386, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_44373, c_42])).
% 56.59/46.22  tff(c_44404, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44386, c_48])).
% 56.59/46.22  tff(c_44372, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_14330])).
% 56.59/46.22  tff(c_44403, plain, (![A_1]: (A_1='#skF_9' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44386, c_42])).
% 56.59/46.22  tff(c_44615, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_44372, c_44403])).
% 56.59/46.22  tff(c_44619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44404, c_44615])).
% 56.59/46.22  tff(c_44621, plain, ('#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_13850])).
% 56.59/46.22  tff(c_44623, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44621, c_48])).
% 56.59/46.22  tff(c_240038, plain, (![A_5788, B_5789, C_5790]: (k2_zfmisc_1(k2_zfmisc_1(A_5788, B_5789), C_5790)=k3_zfmisc_1(A_5788, B_5789, C_5790))), inference(cnfTransformation, [status(thm)], [f_65])).
% 56.59/46.22  tff(c_240054, plain, (![A_5788, B_5789, C_5790]: (v1_xboole_0(k3_zfmisc_1(A_5788, B_5789, C_5790)) | ~v1_xboole_0(k2_zfmisc_1(A_5788, B_5789)))), inference(superposition, [status(thm), theory('equality')], [c_240038, c_14])).
% 56.59/46.22  tff(c_45534, plain, (![A_2497, B_2498, C_2499]: (k2_zfmisc_1(k2_zfmisc_1(A_2497, B_2498), C_2499)=k3_zfmisc_1(A_2497, B_2498, C_2499))), inference(cnfTransformation, [status(thm)], [f_65])).
% 56.59/46.22  tff(c_45550, plain, (![A_2497, B_2498, C_2499]: (v1_xboole_0(k3_zfmisc_1(A_2497, B_2498, C_2499)) | ~v1_xboole_0(k2_zfmisc_1(A_2497, B_2498)))), inference(superposition, [status(thm), theory('equality')], [c_45534, c_14])).
% 56.59/46.22  tff(c_44622, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_44621, c_13861])).
% 56.59/46.22  tff(c_45665, plain, (![A_2512, B_2513, C_2514, D_2515]: (k2_zfmisc_1(k3_zfmisc_1(A_2512, B_2513, C_2514), D_2515)=k4_zfmisc_1(A_2512, B_2513, C_2514, D_2515))), inference(cnfTransformation, [status(thm)], [f_67])).
% 56.59/46.22  tff(c_47042, plain, (![A_2613, B_2614, C_2615, D_2616]: (v1_xboole_0(k4_zfmisc_1(A_2613, B_2614, C_2615, D_2616)) | ~v1_xboole_0(k3_zfmisc_1(A_2613, B_2614, C_2615)))), inference(superposition, [status(thm), theory('equality')], [c_45665, c_14])).
% 56.59/46.22  tff(c_47074, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_44622, c_47042])).
% 56.59/46.22  tff(c_47208, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_47074])).
% 56.59/46.22  tff(c_47215, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_7'))), inference(resolution, [status(thm)], [c_45550, c_47208])).
% 56.59/46.22  tff(c_47224, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_47215])).
% 56.59/46.22  tff(c_44620, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_13850])).
% 56.59/46.22  tff(c_44628, plain, ('#skF_7'!='#skF_3'), inference(splitLeft, [status(thm)], [c_44620])).
% 56.59/46.22  tff(c_45547, plain, (![A_2497, B_2498, C_2499]: (v1_xboole_0(k3_zfmisc_1(A_2497, B_2498, C_2499)) | ~v1_xboole_0(C_2499))), inference(superposition, [status(thm), theory('equality')], [c_45534, c_12])).
% 56.59/46.22  tff(c_46494, plain, (![A_2589, B_2590, C_2591, D_2592]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_2589, B_2590, C_2591, D_2592)), k3_zfmisc_1(A_2589, B_2590, C_2591)))), inference(superposition, [status(thm), theory('equality')], [c_45665, c_22])).
% 56.59/46.22  tff(c_46523, plain, (r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_44622, c_46494])).
% 56.59/46.22  tff(c_46829, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))=k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(resolution, [status(thm)], [c_46523, c_6])).
% 56.59/46.22  tff(c_47270, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(splitLeft, [status(thm)], [c_46829])).
% 56.59/46.22  tff(c_45686, plain, (![A_2512, B_2513, C_2514, D_2515]: (v1_relat_1(k4_zfmisc_1(A_2512, B_2513, C_2514, D_2515)))), inference(superposition, [status(thm), theory('equality')], [c_45665, c_20])).
% 56.59/46.22  tff(c_45882, plain, (![B_2542, A_2543, D_2544, C_2545]: (~r1_tarski(k2_zfmisc_1(B_2542, A_2543), k2_zfmisc_1(D_2544, C_2545)) | r1_tarski(B_2542, D_2544) | v1_xboole_0(A_2543))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_51292, plain, (![B_2825, D_2829, C_2824, C_2827, D_2826, A_2828]: (~r1_tarski(k4_zfmisc_1(A_2828, B_2825, C_2824, D_2826), k2_zfmisc_1(D_2829, C_2827)) | r1_tarski(k3_zfmisc_1(A_2828, B_2825, C_2824), D_2829) | v1_xboole_0(D_2826))), inference(superposition, [status(thm), theory('equality')], [c_28, c_45882])).
% 56.59/46.22  tff(c_51369, plain, (![D_2829, C_2827]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_2829, C_2827)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_2829) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_44622, c_51292])).
% 56.59/46.22  tff(c_51495, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_51369])).
% 56.59/46.22  tff(c_51550, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_51495, c_42])).
% 56.59/46.22  tff(c_45943, plain, (![A_2548, B_2549, C_2550, D_2551]: (v1_xboole_0(k4_zfmisc_1(A_2548, B_2549, C_2550, D_2551)) | ~v1_xboole_0(D_2551))), inference(superposition, [status(thm), theory('equality')], [c_45665, c_12])).
% 56.59/46.22  tff(c_45971, plain, (![A_2548, B_2549, C_2550, D_2551]: (k4_zfmisc_1(A_2548, B_2549, C_2550, D_2551)='#skF_1' | ~v1_xboole_0(D_2551))), inference(resolution, [status(thm)], [c_45943, c_42])).
% 56.59/46.22  tff(c_51546, plain, (![A_2548, B_2549, C_2550]: (k4_zfmisc_1(A_2548, B_2549, C_2550, '#skF_9')='#skF_1')), inference(resolution, [status(thm)], [c_51495, c_45971])).
% 56.59/46.22  tff(c_52430, plain, (![A_2548, B_2549, C_2550]: (k4_zfmisc_1(A_2548, B_2549, C_2550, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_51550, c_51546])).
% 56.59/46.22  tff(c_51598, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_51550, c_44623])).
% 56.59/46.22  tff(c_52439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52430, c_51598])).
% 56.59/46.22  tff(c_53595, plain, (![D_2895, C_2896]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_2895, C_2896)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_2895))), inference(splitRight, [status(thm)], [c_51369])).
% 56.59/46.22  tff(c_53632, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))) | ~v1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(resolution, [status(thm)], [c_24, c_53595])).
% 56.59/46.22  tff(c_53646, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_45686, c_53632])).
% 56.59/46.22  tff(c_53648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47270, c_53646])).
% 56.59/46.22  tff(c_53649, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))=k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_46829])).
% 56.59/46.22  tff(c_45684, plain, (![A_2512, B_2513, C_2514, D_2515]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_2512, B_2513, C_2514, D_2515)), k3_zfmisc_1(A_2512, B_2513, C_2514)))), inference(superposition, [status(thm), theory('equality')], [c_45665, c_22])).
% 56.59/46.22  tff(c_53975, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_53649, c_45684])).
% 56.59/46.22  tff(c_44629, plain, (![A_1919, B_1920]: (k2_zfmisc_1(A_1919, B_1920)='#skF_1' | ~v1_xboole_0(A_1919))), inference(resolution, [status(thm)], [c_56, c_42])).
% 56.59/46.22  tff(c_44649, plain, (![B_1923]: (k2_zfmisc_1('#skF_1', B_1923)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_44629])).
% 56.59/46.22  tff(c_44660, plain, (r1_tarski(k1_relat_1('#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44649, c_22])).
% 56.59/46.22  tff(c_44672, plain, (k1_relat_1('#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_44660, c_6])).
% 56.59/46.22  tff(c_44722, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44672])).
% 56.59/46.22  tff(c_44638, plain, (![B_1920]: (k2_zfmisc_1('#skF_1', B_1920)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_44629])).
% 56.59/46.22  tff(c_45110, plain, (![B_1977, A_1978, D_1979, C_1980]: (~r1_tarski(k2_zfmisc_1(B_1977, A_1978), k2_zfmisc_1(D_1979, C_1980)) | r1_tarski(B_1977, D_1979) | v1_xboole_0(A_1978))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_45120, plain, (![B_1977, A_1978]: (r1_tarski(B_1977, k1_relat_1(k2_zfmisc_1(B_1977, A_1978))) | v1_xboole_0(A_1978) | ~v1_relat_1(k2_zfmisc_1(B_1977, A_1978)))), inference(resolution, [status(thm)], [c_24, c_45110])).
% 56.59/46.22  tff(c_45366, plain, (![B_2251, A_2252]: (r1_tarski(B_2251, k1_relat_1(k2_zfmisc_1(B_2251, A_2252))) | v1_xboole_0(A_2252))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_45120])).
% 56.59/46.22  tff(c_45383, plain, (![B_1920]: (r1_tarski('#skF_1', k1_relat_1('#skF_1')) | v1_xboole_0(B_1920))), inference(superposition, [status(thm), theory('equality')], [c_44638, c_45366])).
% 56.59/46.22  tff(c_45389, plain, (![B_1920]: (v1_xboole_0(B_1920))), inference(negUnitSimplification, [status(thm)], [c_44722, c_45383])).
% 56.59/46.22  tff(c_45412, plain, (![A_2254]: (A_2254='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45389, c_42])).
% 56.59/46.22  tff(c_45467, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45412, c_44722])).
% 56.59/46.22  tff(c_45526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_45467])).
% 56.59/46.22  tff(c_45527, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_44672])).
% 56.59/46.22  tff(c_44677, plain, (![A_1924, B_1925]: (k2_zfmisc_1(A_1924, B_1925)='#skF_1' | ~v1_xboole_0(B_1925))), inference(resolution, [status(thm)], [c_13856, c_42])).
% 56.59/46.22  tff(c_44687, plain, (![A_1926]: (k2_zfmisc_1(A_1926, '#skF_1')='#skF_1')), inference(resolution, [status(thm)], [c_4, c_44677])).
% 56.59/46.22  tff(c_44701, plain, (![A_1926]: (r1_tarski(k1_relat_1('#skF_1'), A_1926))), inference(superposition, [status(thm), theory('equality')], [c_44687, c_22])).
% 56.59/46.22  tff(c_45529, plain, (![A_1926]: (r1_tarski('#skF_1', A_1926))), inference(demodulation, [status(thm), theory('equality')], [c_45527, c_44701])).
% 56.59/46.22  tff(c_46238, plain, (![A_2576, A_2577, B_2578]: (k2_zfmisc_1(A_2576, k2_zfmisc_1(A_2577, B_2578))='#skF_1' | ~v1_xboole_0(B_2578))), inference(resolution, [status(thm)], [c_12, c_44677])).
% 56.59/46.22  tff(c_46271, plain, (![B_2578, D_14, A_2576, A_2577, C_13]: (~r1_tarski('#skF_1', k2_zfmisc_1(C_13, D_14)) | r1_tarski(k2_zfmisc_1(A_2577, B_2578), D_14) | v1_xboole_0(A_2576) | ~v1_xboole_0(B_2578))), inference(superposition, [status(thm), theory('equality')], [c_46238, c_18])).
% 56.59/46.22  tff(c_46344, plain, (![A_2577, B_2578, D_14, A_2576]: (r1_tarski(k2_zfmisc_1(A_2577, B_2578), D_14) | v1_xboole_0(A_2576) | ~v1_xboole_0(B_2578))), inference(demodulation, [status(thm), theory('equality')], [c_45529, c_46271])).
% 56.59/46.22  tff(c_53652, plain, (![A_2897, B_2898, D_2899]: (r1_tarski(k2_zfmisc_1(A_2897, B_2898), D_2899) | ~v1_xboole_0(B_2898))), inference(splitLeft, [status(thm)], [c_46344])).
% 56.59/46.22  tff(c_53695, plain, (![B_2898, D_14, A_2897]: (r1_tarski(B_2898, D_14) | v1_xboole_0(A_2897) | ~v1_xboole_0(B_2898))), inference(resolution, [status(thm)], [c_53652, c_18])).
% 56.59/46.22  tff(c_53705, plain, (![B_2900, D_2901]: (r1_tarski(B_2900, D_2901) | ~v1_xboole_0(B_2900))), inference(splitLeft, [status(thm)], [c_53695])).
% 56.59/46.22  tff(c_53726, plain, (![D_2901, B_2900]: (D_2901=B_2900 | ~r1_tarski(D_2901, B_2900) | ~v1_xboole_0(B_2900))), inference(resolution, [status(thm)], [c_53705, c_6])).
% 56.59/46.22  tff(c_54131, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_53975, c_53726])).
% 56.59/46.22  tff(c_54462, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_54131])).
% 56.59/46.22  tff(c_54470, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_45547, c_54462])).
% 56.59/46.22  tff(c_47216, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_45547, c_47208])).
% 56.59/46.22  tff(c_56906, plain, (![B_3054, D_3058, C_3053, C_3056, A_3057, D_3055]: (~r1_tarski(k4_zfmisc_1(A_3057, B_3054, C_3053, D_3055), k2_zfmisc_1(D_3058, C_3056)) | r1_tarski(k3_zfmisc_1(A_3057, B_3054, C_3053), D_3058) | v1_xboole_0(D_3055))), inference(superposition, [status(thm), theory('equality')], [c_28, c_45882])).
% 56.59/46.22  tff(c_56980, plain, (![D_3058, C_3056]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_3058, C_3056)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_3058) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_44622, c_56906])).
% 56.59/46.22  tff(c_57011, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_56980])).
% 56.59/46.22  tff(c_57054, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_57011, c_42])).
% 56.59/46.22  tff(c_57050, plain, (![A_2548, B_2549, C_2550]: (k4_zfmisc_1(A_2548, B_2549, C_2550, '#skF_9')='#skF_1')), inference(resolution, [status(thm)], [c_57011, c_45971])).
% 56.59/46.22  tff(c_57866, plain, (![A_2548, B_2549, C_2550]: (k4_zfmisc_1(A_2548, B_2549, C_2550, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_57054, c_57050])).
% 56.59/46.22  tff(c_57100, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_57054, c_44623])).
% 56.59/46.22  tff(c_57876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57866, c_57100])).
% 56.59/46.22  tff(c_57878, plain, (~v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_56980])).
% 56.59/46.22  tff(c_54132, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_53975, c_6])).
% 56.59/46.22  tff(c_55624, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_54132])).
% 56.59/46.22  tff(c_58228, plain, (![A_3108, A_3107, B_3105, B_3104, C_3103, D_3106]: (~r1_tarski(k2_zfmisc_1(B_3105, A_3107), k4_zfmisc_1(A_3108, B_3104, C_3103, D_3106)) | r1_tarski(B_3105, k3_zfmisc_1(A_3108, B_3104, C_3103)) | v1_xboole_0(A_3107))), inference(superposition, [status(thm), theory('equality')], [c_28, c_45882])).
% 56.59/46.22  tff(c_58333, plain, (![B_3109, A_3110]: (~r1_tarski(k2_zfmisc_1(B_3109, A_3110), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(B_3109, k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(A_3110))), inference(superposition, [status(thm), theory('equality')], [c_44622, c_58228])).
% 56.59/46.22  tff(c_60328, plain, (![A_3184, B_3185, C_3186, D_3187]: (~r1_tarski(k4_zfmisc_1(A_3184, B_3185, C_3186, D_3187), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(k3_zfmisc_1(A_3184, B_3185, C_3186), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(D_3187))), inference(superposition, [status(thm), theory('equality')], [c_28, c_58333])).
% 56.59/46.22  tff(c_60381, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_10, c_60328])).
% 56.59/46.22  tff(c_60416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57878, c_55624, c_60381])).
% 56.59/46.22  tff(c_60417, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54132])).
% 56.59/46.22  tff(c_45892, plain, (![B_2542, A_2543]: (r1_tarski(B_2542, k1_relat_1(k2_zfmisc_1(B_2542, A_2543))) | v1_xboole_0(A_2543) | ~v1_relat_1(k2_zfmisc_1(B_2542, A_2543)))), inference(resolution, [status(thm)], [c_24, c_45882])).
% 56.59/46.22  tff(c_45977, plain, (![B_2552, A_2553]: (r1_tarski(B_2552, k1_relat_1(k2_zfmisc_1(B_2552, A_2553))) | v1_xboole_0(A_2553))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_45892])).
% 56.59/46.22  tff(c_45979, plain, (![B_2552, A_2553]: (k1_relat_1(k2_zfmisc_1(B_2552, A_2553))=B_2552 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(B_2552, A_2553)), B_2552) | v1_xboole_0(A_2553))), inference(resolution, [status(thm)], [c_45977, c_6])).
% 56.59/46.22  tff(c_45997, plain, (![B_2554, A_2555]: (k1_relat_1(k2_zfmisc_1(B_2554, A_2555))=B_2554 | v1_xboole_0(A_2555))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_45979])).
% 56.59/46.22  tff(c_46018, plain, (![A_20, B_21, C_22]: (k1_relat_1(k3_zfmisc_1(A_20, B_21, C_22))=k2_zfmisc_1(A_20, B_21) | v1_xboole_0(C_22))), inference(superposition, [status(thm), theory('equality')], [c_26, c_45997])).
% 56.59/46.22  tff(c_60426, plain, (k1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_2', '#skF_7') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_60417, c_46018])).
% 56.59/46.22  tff(c_60461, plain, (k1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_2', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_47216, c_60426])).
% 56.59/46.22  tff(c_60471, plain, (k2_zfmisc_1('#skF_2', '#skF_7')=k2_zfmisc_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60461, c_46018])).
% 56.59/46.22  tff(c_60483, plain, (k2_zfmisc_1('#skF_2', '#skF_7')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54470, c_60471])).
% 56.59/46.22  tff(c_60570, plain, (![C_13, D_14]: (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1(C_13, D_14)) | r1_tarski('#skF_7', D_14) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_60483, c_18])).
% 56.59/46.22  tff(c_63793, plain, (![C_3296, D_3297]: (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1(C_3296, D_3297)) | r1_tarski('#skF_7', D_3297))), inference(negUnitSimplification, [status(thm)], [c_47224, c_60570])).
% 56.59/46.22  tff(c_63852, plain, (r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_63793])).
% 56.59/46.22  tff(c_63857, plain, ('#skF_7'='#skF_3' | ~r1_tarski('#skF_3', '#skF_7')), inference(resolution, [status(thm)], [c_63852, c_6])).
% 56.59/46.22  tff(c_63862, plain, (~r1_tarski('#skF_3', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44628, c_63857])).
% 56.59/46.22  tff(c_238664, plain, (![A_5462, B_5463]: (~r1_tarski(k2_zfmisc_1(A_5462, B_5463), k2_zfmisc_1('#skF_2', '#skF_3')) | r1_tarski(B_5463, '#skF_7') | v1_xboole_0(A_5462))), inference(superposition, [status(thm), theory('equality')], [c_60483, c_18])).
% 56.59/46.22  tff(c_238890, plain, (r1_tarski('#skF_3', '#skF_7') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_238664])).
% 56.59/46.22  tff(c_239014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47224, c_63862, c_238890])).
% 56.59/46.22  tff(c_239016, plain, (v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_54131])).
% 56.59/46.22  tff(c_239059, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_239016, c_42])).
% 56.59/46.22  tff(c_239061, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_239059, c_53975])).
% 56.59/46.22  tff(c_45576, plain, (![A_2500]: (r1_tarski('#skF_1', A_2500))), inference(demodulation, [status(thm), theory('equality')], [c_45527, c_44701])).
% 56.59/46.22  tff(c_45579, plain, (![A_2500]: (A_2500='#skF_1' | ~r1_tarski(A_2500, '#skF_1'))), inference(resolution, [status(thm)], [c_45576, c_6])).
% 56.59/46.22  tff(c_239111, plain, (k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')='#skF_1'), inference(resolution, [status(thm)], [c_239061, c_45579])).
% 56.59/46.22  tff(c_239251, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_239111, c_47208])).
% 56.59/46.22  tff(c_239255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_239251])).
% 56.59/46.22  tff(c_239256, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_47074])).
% 56.59/46.22  tff(c_239332, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_1'), inference(resolution, [status(thm)], [c_239256, c_42])).
% 56.59/46.22  tff(c_239343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44623, c_239332])).
% 56.59/46.22  tff(c_239345, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_44620])).
% 56.59/46.22  tff(c_239404, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_239345, c_44622])).
% 56.59/46.22  tff(c_240169, plain, (![A_5803, B_5804, C_5805, D_5806]: (k2_zfmisc_1(k3_zfmisc_1(A_5803, B_5804, C_5805), D_5806)=k4_zfmisc_1(A_5803, B_5804, C_5805, D_5806))), inference(cnfTransformation, [status(thm)], [f_67])).
% 56.59/46.22  tff(c_241546, plain, (![A_5904, B_5905, C_5906, D_5907]: (v1_xboole_0(k4_zfmisc_1(A_5904, B_5905, C_5906, D_5907)) | ~v1_xboole_0(k3_zfmisc_1(A_5904, B_5905, C_5906)))), inference(superposition, [status(thm), theory('equality')], [c_240169, c_14])).
% 56.59/46.22  tff(c_241578, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_239404, c_241546])).
% 56.59/46.22  tff(c_241712, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(splitLeft, [status(thm)], [c_241578])).
% 56.59/46.22  tff(c_241719, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_240054, c_241712])).
% 56.59/46.22  tff(c_239344, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_44620])).
% 56.59/46.22  tff(c_240386, plain, (![B_5833, A_5834, D_5835, C_5836]: (~r1_tarski(k2_zfmisc_1(B_5833, A_5834), k2_zfmisc_1(D_5835, C_5836)) | r1_tarski(B_5833, D_5835) | v1_xboole_0(A_5834))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_250617, plain, (![D_6322, A_6323, C_6319, D_6321, C_6324, B_6320]: (~r1_tarski(k4_zfmisc_1(A_6323, B_6320, C_6319, D_6321), k2_zfmisc_1(D_6322, C_6324)) | r1_tarski(k3_zfmisc_1(A_6323, B_6320, C_6319), D_6322) | v1_xboole_0(D_6321))), inference(superposition, [status(thm), theory('equality')], [c_28, c_240386])).
% 56.59/46.22  tff(c_250694, plain, (![D_6322, C_6324]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_6322, C_6324)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), D_6322) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_239404, c_250617])).
% 56.59/46.22  tff(c_250727, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_250694])).
% 56.59/46.22  tff(c_250770, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_250727, c_42])).
% 56.59/46.22  tff(c_240447, plain, (![A_5839, B_5840, C_5841, D_5842]: (v1_xboole_0(k4_zfmisc_1(A_5839, B_5840, C_5841, D_5842)) | ~v1_xboole_0(D_5842))), inference(superposition, [status(thm), theory('equality')], [c_240169, c_12])).
% 56.59/46.22  tff(c_240475, plain, (![A_5839, B_5840, C_5841, D_5842]: (k4_zfmisc_1(A_5839, B_5840, C_5841, D_5842)='#skF_1' | ~v1_xboole_0(D_5842))), inference(resolution, [status(thm)], [c_240447, c_42])).
% 56.59/46.22  tff(c_250766, plain, (![A_5839, B_5840, C_5841]: (k4_zfmisc_1(A_5839, B_5840, C_5841, '#skF_9')='#skF_1')), inference(resolution, [status(thm)], [c_250727, c_240475])).
% 56.59/46.22  tff(c_251586, plain, (![A_5839, B_5840, C_5841]: (k4_zfmisc_1(A_5839, B_5840, C_5841, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_250770, c_250766])).
% 56.59/46.22  tff(c_250817, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_250770, c_44623])).
% 56.59/46.22  tff(c_251596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251586, c_250817])).
% 56.59/46.22  tff(c_251598, plain, (~v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_250694])).
% 56.59/46.22  tff(c_240998, plain, (![A_5880, B_5881, C_5882, D_5883]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_5880, B_5881, C_5882, D_5883)), k3_zfmisc_1(A_5880, B_5881, C_5882)))), inference(superposition, [status(thm), theory('equality')], [c_240169, c_22])).
% 56.59/46.22  tff(c_241027, plain, (r1_tarski(k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_239404, c_240998])).
% 56.59/46.22  tff(c_241333, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(resolution, [status(thm)], [c_241027, c_6])).
% 56.59/46.22  tff(c_241774, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(splitLeft, [status(thm)], [c_241333])).
% 56.59/46.22  tff(c_240190, plain, (![A_5803, B_5804, C_5805, D_5806]: (v1_relat_1(k4_zfmisc_1(A_5803, B_5804, C_5805, D_5806)))), inference(superposition, [status(thm), theory('equality')], [c_240169, c_20])).
% 56.59/46.22  tff(c_240182, plain, (![A_5803, B_5804, C_5805, D_5806]: (v1_xboole_0(k4_zfmisc_1(A_5803, B_5804, C_5805, D_5806)) | ~v1_xboole_0(D_5806))), inference(superposition, [status(thm), theory('equality')], [c_240169, c_12])).
% 56.59/46.22  tff(c_239350, plain, (![A_5469, B_5470]: (k2_zfmisc_1(A_5469, B_5470)='#skF_1' | ~v1_xboole_0(A_5469))), inference(resolution, [status(thm)], [c_56, c_42])).
% 56.59/46.22  tff(c_239360, plain, (![B_5471]: (k2_zfmisc_1('#skF_1', B_5471)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_239350])).
% 56.59/46.22  tff(c_239371, plain, (r1_tarski(k1_relat_1('#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_239360, c_22])).
% 56.59/46.22  tff(c_239393, plain, (k1_relat_1('#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_239371, c_6])).
% 56.59/46.22  tff(c_239444, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_239393])).
% 56.59/46.22  tff(c_239359, plain, (![B_5470]: (k2_zfmisc_1('#skF_1', B_5470)='#skF_1')), inference(resolution, [status(thm)], [c_4, c_239350])).
% 56.59/46.22  tff(c_239681, plain, (![B_5510, A_5511, D_5512, C_5513]: (~r1_tarski(k2_zfmisc_1(B_5510, A_5511), k2_zfmisc_1(D_5512, C_5513)) | r1_tarski(B_5510, D_5512) | v1_xboole_0(A_5511))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_239691, plain, (![B_5510, A_5511]: (r1_tarski(B_5510, k1_relat_1(k2_zfmisc_1(B_5510, A_5511))) | v1_xboole_0(A_5511) | ~v1_relat_1(k2_zfmisc_1(B_5510, A_5511)))), inference(resolution, [status(thm)], [c_24, c_239681])).
% 56.59/46.22  tff(c_239832, plain, (![B_5527, A_5528]: (r1_tarski(B_5527, k1_relat_1(k2_zfmisc_1(B_5527, A_5528))) | v1_xboole_0(A_5528))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_239691])).
% 56.59/46.22  tff(c_239849, plain, (![B_5470]: (r1_tarski('#skF_1', k1_relat_1('#skF_1')) | v1_xboole_0(B_5470))), inference(superposition, [status(thm), theory('equality')], [c_239359, c_239832])).
% 56.59/46.22  tff(c_239855, plain, (![B_5470]: (v1_xboole_0(B_5470))), inference(negUnitSimplification, [status(thm)], [c_239444, c_239849])).
% 56.59/46.22  tff(c_239916, plain, (![A_5534]: (A_5534='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_239855, c_42])).
% 56.59/46.22  tff(c_239971, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_239916, c_239444])).
% 56.59/46.22  tff(c_240030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_239971])).
% 56.59/46.22  tff(c_240031, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_239393])).
% 56.59/46.22  tff(c_239394, plain, (![A_5474, B_5475]: (k2_zfmisc_1(A_5474, B_5475)='#skF_1' | ~v1_xboole_0(B_5475))), inference(resolution, [status(thm)], [c_13856, c_42])).
% 56.59/46.22  tff(c_239409, plain, (![A_5476]: (k2_zfmisc_1(A_5476, '#skF_1')='#skF_1')), inference(resolution, [status(thm)], [c_4, c_239394])).
% 56.59/46.22  tff(c_239423, plain, (![A_5476]: (r1_tarski(k1_relat_1('#skF_1'), A_5476))), inference(superposition, [status(thm), theory('equality')], [c_239409, c_22])).
% 56.59/46.22  tff(c_240033, plain, (![A_5476]: (r1_tarski('#skF_1', A_5476))), inference(demodulation, [status(thm), theory('equality')], [c_240031, c_239423])).
% 56.59/46.22  tff(c_240742, plain, (![A_5867, A_5868, B_5869]: (k2_zfmisc_1(A_5867, k2_zfmisc_1(A_5868, B_5869))='#skF_1' | ~v1_xboole_0(A_5868))), inference(resolution, [status(thm)], [c_14, c_239394])).
% 56.59/46.22  tff(c_240775, plain, (![A_5867, B_5869, D_14, A_5868, C_13]: (~r1_tarski('#skF_1', k2_zfmisc_1(C_13, D_14)) | r1_tarski(k2_zfmisc_1(A_5868, B_5869), D_14) | v1_xboole_0(A_5867) | ~v1_xboole_0(A_5868))), inference(superposition, [status(thm), theory('equality')], [c_240742, c_18])).
% 56.59/46.22  tff(c_240848, plain, (![A_5868, B_5869, D_14, A_5867]: (r1_tarski(k2_zfmisc_1(A_5868, B_5869), D_14) | v1_xboole_0(A_5867) | ~v1_xboole_0(A_5868))), inference(demodulation, [status(thm), theory('equality')], [c_240033, c_240775])).
% 56.59/46.22  tff(c_241776, plain, (![A_5914, B_5915, D_5916]: (r1_tarski(k2_zfmisc_1(A_5914, B_5915), D_5916) | ~v1_xboole_0(A_5914))), inference(splitLeft, [status(thm)], [c_240848])).
% 56.59/46.22  tff(c_241818, plain, (![A_5914, D_14, B_5915]: (r1_tarski(A_5914, D_14) | v1_xboole_0(B_5915) | ~v1_xboole_0(A_5914))), inference(resolution, [status(thm)], [c_241776, c_16])).
% 56.59/46.22  tff(c_241828, plain, (![A_5914, D_14]: (r1_tarski(A_5914, D_14) | ~v1_xboole_0(A_5914))), inference(splitLeft, [status(thm)], [c_241818])).
% 56.59/46.22  tff(c_240271, plain, (![A_5820, B_5821, C_5822, D_5823]: (~r1_tarski(k2_zfmisc_1(A_5820, B_5821), k2_zfmisc_1(C_5822, D_5823)) | r1_tarski(B_5821, D_5823) | v1_xboole_0(A_5820))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.59/46.22  tff(c_245786, plain, (![D_6120, C_6119, A_6121, B_6118, C_6117, D_6122]: (~r1_tarski(k4_zfmisc_1(A_6121, B_6118, C_6117, D_6120), k2_zfmisc_1(C_6119, D_6122)) | r1_tarski(D_6120, D_6122) | v1_xboole_0(k3_zfmisc_1(A_6121, B_6118, C_6117)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_240271])).
% 56.59/46.22  tff(c_245863, plain, (![C_6119, D_6122]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(C_6119, D_6122)) | r1_tarski('#skF_9', D_6122) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_239404, c_245786])).
% 56.59/46.22  tff(c_245943, plain, (![C_6126, D_6127]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(C_6126, D_6127)) | r1_tarski('#skF_9', D_6127))), inference(negUnitSimplification, [status(thm)], [c_241712, c_245863])).
% 56.59/46.22  tff(c_245985, plain, (![D_6127]: (r1_tarski('#skF_9', D_6127) | ~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(resolution, [status(thm)], [c_241828, c_245943])).
% 56.59/46.22  tff(c_245996, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitLeft, [status(thm)], [c_245985])).
% 56.59/46.22  tff(c_246004, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_240182, c_245996])).
% 56.59/46.22  tff(c_246013, plain, (![D_6131, A_6132, D_6130, C_6133, C_6128, B_6129]: (~r1_tarski(k4_zfmisc_1(A_6132, B_6129, C_6128, D_6130), k2_zfmisc_1(D_6131, C_6133)) | r1_tarski(k3_zfmisc_1(A_6132, B_6129, C_6128), D_6131) | v1_xboole_0(D_6130))), inference(superposition, [status(thm), theory('equality')], [c_28, c_240386])).
% 56.59/46.22  tff(c_246090, plain, (![D_6131, C_6133]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_6131, C_6133)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), D_6131) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_239404, c_246013])).
% 56.59/46.22  tff(c_246133, plain, (![D_6134, C_6135]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_6134, C_6135)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), D_6134))), inference(negUnitSimplification, [status(thm)], [c_246004, c_246090])).
% 56.59/46.22  tff(c_246164, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))) | ~v1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(resolution, [status(thm)], [c_24, c_246133])).
% 56.59/46.22  tff(c_246178, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_240190, c_246164])).
% 56.59/46.22  tff(c_246180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241774, c_246178])).
% 56.59/46.22  tff(c_246185, plain, (![D_6136]: (r1_tarski('#skF_9', D_6136))), inference(splitRight, [status(thm)], [c_245985])).
% 56.59/46.22  tff(c_240080, plain, (![A_5791]: (r1_tarski('#skF_1', A_5791))), inference(demodulation, [status(thm), theory('equality')], [c_240031, c_239423])).
% 56.59/46.22  tff(c_240083, plain, (![A_5791]: (A_5791='#skF_1' | ~r1_tarski(A_5791, '#skF_1'))), inference(resolution, [status(thm)], [c_240080, c_6])).
% 56.59/46.22  tff(c_246201, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_246185, c_240083])).
% 56.59/46.22  tff(c_246250, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_246201, c_44623])).
% 56.59/46.22  tff(c_246182, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_245985])).
% 56.59/46.22  tff(c_246251, plain, (![A_1]: (A_1='#skF_9' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_246201, c_42])).
% 56.59/46.22  tff(c_247052, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_246182, c_246251])).
% 56.59/46.22  tff(c_247072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246250, c_247052])).
% 56.59/46.22  tff(c_247073, plain, (![B_5915]: (v1_xboole_0(B_5915))), inference(splitRight, [status(thm)], [c_241818])).
% 56.59/46.22  tff(c_241728, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_241719])).
% 56.59/46.22  tff(c_247140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247073, c_241728])).
% 56.59/46.22  tff(c_247141, plain, (![A_5867]: (v1_xboole_0(A_5867))), inference(splitRight, [status(thm)], [c_240848])).
% 56.59/46.22  tff(c_247206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247141, c_241728])).
% 56.59/46.22  tff(c_247207, plain, (k1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_241333])).
% 56.59/46.22  tff(c_240188, plain, (![A_5803, B_5804, C_5805, D_5806]: (r1_tarski(k1_relat_1(k4_zfmisc_1(A_5803, B_5804, C_5805, D_5806)), k3_zfmisc_1(A_5803, B_5804, C_5805)))), inference(superposition, [status(thm), theory('equality')], [c_240169, c_22])).
% 56.59/46.22  tff(c_247511, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_247207, c_240188])).
% 56.59/46.22  tff(c_247639, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4') | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(resolution, [status(thm)], [c_247511, c_6])).
% 56.59/46.22  tff(c_249174, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(splitLeft, [status(thm)], [c_247639])).
% 56.59/46.22  tff(c_251599, plain, (![A_6357, C_6356, A_6361, D_6359, B_6360, B_6358]: (~r1_tarski(k2_zfmisc_1(B_6360, A_6357), k4_zfmisc_1(A_6361, B_6358, C_6356, D_6359)) | r1_tarski(B_6360, k3_zfmisc_1(A_6361, B_6358, C_6356)) | v1_xboole_0(A_6357))), inference(superposition, [status(thm), theory('equality')], [c_28, c_240386])).
% 56.59/46.22  tff(c_251704, plain, (![B_6362, A_6363]: (~r1_tarski(k2_zfmisc_1(B_6362, A_6363), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(B_6362, k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | v1_xboole_0(A_6363))), inference(superposition, [status(thm), theory('equality')], [c_239404, c_251599])).
% 56.59/46.22  tff(c_253883, plain, (![A_6445, B_6446, C_6447, D_6448]: (~r1_tarski(k4_zfmisc_1(A_6445, B_6446, C_6447, D_6448), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(k3_zfmisc_1(A_6445, B_6446, C_6447), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | v1_xboole_0(D_6448))), inference(superposition, [status(thm), theory('equality')], [c_28, c_251704])).
% 56.59/46.22  tff(c_253936, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_10, c_253883])).
% 56.59/46.22  tff(c_253971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251598, c_249174, c_253936])).
% 56.59/46.22  tff(c_253972, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')=k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_247639])).
% 56.59/46.22  tff(c_254093, plain, (![C_6453, D_6456, B_6454, C_6452, A_6455]: (~r1_tarski(k3_zfmisc_1(A_6455, B_6454, C_6452), k2_zfmisc_1(C_6453, D_6456)) | r1_tarski(C_6452, D_6456) | v1_xboole_0(k2_zfmisc_1(A_6455, B_6454)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_240271])).
% 56.59/46.22  tff(c_254096, plain, (![C_6453, D_6456]: (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1(C_6453, D_6456)) | r1_tarski('#skF_8', D_6456) | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_253972, c_254093])).
% 56.59/46.22  tff(c_255040, plain, (![C_6485, D_6486]: (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1(C_6485, D_6486)) | r1_tarski('#skF_8', D_6486))), inference(negUnitSimplification, [status(thm)], [c_241719, c_254096])).
% 56.59/46.22  tff(c_255829, plain, (![A_6517, B_6518, C_6519]: (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1(A_6517, B_6518, C_6519)) | r1_tarski('#skF_8', C_6519))), inference(superposition, [status(thm), theory('equality')], [c_26, c_255040])).
% 56.59/46.22  tff(c_255880, plain, (r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_255829])).
% 56.59/46.22  tff(c_255885, plain, ('#skF_8'='#skF_4' | ~r1_tarski('#skF_4', '#skF_8')), inference(resolution, [status(thm)], [c_255880, c_6])).
% 56.59/46.22  tff(c_255890, plain, (~r1_tarski('#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_239344, c_255885])).
% 56.59/46.22  tff(c_247849, plain, (![B_6206, A_6207, B_6208, C_6205, A_6209]: (~r1_tarski(k2_zfmisc_1(A_6209, B_6208), k3_zfmisc_1(A_6207, B_6206, C_6205)) | r1_tarski(B_6208, C_6205) | v1_xboole_0(A_6209))), inference(superposition, [status(thm), theory('equality')], [c_26, c_240271])).
% 56.59/46.22  tff(c_264856, plain, (![B_6762, A_6763, B_6764, C_6761, A_6766, C_6765]: (~r1_tarski(k3_zfmisc_1(A_6766, B_6764, C_6761), k3_zfmisc_1(A_6763, B_6762, C_6765)) | r1_tarski(C_6761, C_6765) | v1_xboole_0(k2_zfmisc_1(A_6766, B_6764)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_247849])).
% 56.59/46.22  tff(c_428838, plain, (![A_8784, B_8785, C_8786]: (~r1_tarski(k3_zfmisc_1(A_8784, B_8785, C_8786), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(C_8786, '#skF_8') | v1_xboole_0(k2_zfmisc_1(A_8784, B_8785)))), inference(superposition, [status(thm), theory('equality')], [c_253972, c_264856])).
% 56.59/46.22  tff(c_429065, plain, (r1_tarski('#skF_4', '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_428838])).
% 56.59/46.22  tff(c_429189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241719, c_255890, c_429065])).
% 56.59/46.22  tff(c_429190, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_241578])).
% 56.59/46.22  tff(c_429266, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_1'), inference(resolution, [status(thm)], [c_429190, c_42])).
% 56.59/46.22  tff(c_429277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44623, c_429266])).
% 56.59/46.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 56.59/46.22  
% 56.59/46.22  Inference rules
% 56.59/46.22  ----------------------
% 56.59/46.22  #Ref     : 0
% 56.59/46.22  #Sup     : 108418
% 56.59/46.22  #Fact    : 0
% 56.59/46.22  #Define  : 0
% 56.59/46.22  #Split   : 213
% 56.59/46.22  #Chain   : 0
% 56.59/46.22  #Close   : 0
% 56.59/46.22  
% 56.59/46.22  Ordering : KBO
% 56.59/46.22  
% 56.59/46.22  Simplification rules
% 56.59/46.22  ----------------------
% 56.59/46.22  #Subsume      : 17850
% 56.59/46.22  #Demod        : 103141
% 56.59/46.22  #Tautology    : 67800
% 56.59/46.22  #SimpNegUnit  : 441
% 56.59/46.22  #BackRed      : 1526
% 56.59/46.22  
% 56.59/46.22  #Partial instantiations: 267
% 56.59/46.22  #Strategies tried      : 1
% 56.59/46.22  
% 56.59/46.22  Timing (in seconds)
% 56.59/46.22  ----------------------
% 56.59/46.22  Preprocessing        : 0.30
% 56.59/46.22  Parsing              : 0.16
% 56.59/46.22  CNF conversion       : 0.02
% 56.59/46.22  Main loop            : 44.95
% 56.59/46.22  Inferencing          : 7.02
% 56.59/46.22  Reduction            : 14.43
% 56.59/46.22  Demodulation         : 11.01
% 56.59/46.22  BG Simplification    : 0.73
% 56.59/46.22  Subsumption          : 19.79
% 56.59/46.22  Abstraction          : 1.17
% 56.59/46.22  MUC search           : 0.00
% 56.59/46.22  Cooper               : 0.00
% 56.59/46.22  Total                : 45.44
% 56.59/46.22  Index Insertion      : 0.00
% 56.59/46.22  Index Deletion       : 0.00
% 56.59/46.22  Index Matching       : 0.00
% 56.59/46.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
