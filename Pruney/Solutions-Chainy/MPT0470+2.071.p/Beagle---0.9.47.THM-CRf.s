%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 193 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 ( 346 expanded)
%              Number of equality atoms :   56 ( 107 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_105,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_81,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    ! [A_38] :
      ( v1_relat_1(A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k5_relat_1(A_24,B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [B_19] : k2_zfmisc_1(k1_xboole_0,B_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_337,plain,(
    ! [A_77,B_78] :
      ( k1_relat_1(k5_relat_1(A_77,B_78)) = k1_relat_1(A_77)
      | ~ r1_tarski(k2_relat_1(A_77),k1_relat_1(B_78))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_349,plain,(
    ! [B_78] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_78)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_78))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_337])).

tff(c_354,plain,(
    ! [B_79] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_79)) = k1_xboole_0
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8,c_48,c_349])).

tff(c_36,plain,(
    ! [A_28] :
      ( k3_xboole_0(A_28,k2_zfmisc_1(k1_relat_1(A_28),k2_relat_1(A_28))) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_366,plain,(
    ! [B_79] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_79),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_79)))) = k5_relat_1(k1_xboole_0,B_79)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_36])).

tff(c_375,plain,(
    ! [B_80] :
      ( k5_relat_1(k1_xboole_0,B_80) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22,c_366])).

tff(c_379,plain,(
    ! [B_25] :
      ( k5_relat_1(k1_xboole_0,B_25) = k1_xboole_0
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_375])).

tff(c_383,plain,(
    ! [B_81] :
      ( k5_relat_1(k1_xboole_0,B_81) = k1_xboole_0
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_379])).

tff(c_395,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_383])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_395])).

tff(c_403,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_28,plain,(
    ! [A_23] :
      ( v1_relat_1(k4_relat_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_478,plain,(
    ! [A_90] :
      ( k2_relat_1(k4_relat_1(A_90)) = k1_relat_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k2_relat_1(A_26))
      | ~ v1_relat_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_562,plain,(
    ! [A_105] :
      ( ~ v1_xboole_0(k1_relat_1(A_105))
      | ~ v1_relat_1(k4_relat_1(A_105))
      | v1_xboole_0(k4_relat_1(A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_574,plain,(
    ! [A_106] :
      ( k4_relat_1(A_106) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_106))
      | ~ v1_relat_1(k4_relat_1(A_106))
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_562,c_4])).

tff(c_580,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_574])).

tff(c_582,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2,c_580])).

tff(c_583,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_582])).

tff(c_604,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_583])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_604])).

tff(c_609,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_764,plain,(
    ! [A_119,B_120] :
      ( k1_relat_1(k5_relat_1(A_119,B_120)) = k1_relat_1(A_119)
      | ~ r1_tarski(k2_relat_1(A_119),k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_776,plain,(
    ! [B_120] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_120)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_764])).

tff(c_781,plain,(
    ! [B_121] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_121)) = k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8,c_48,c_776])).

tff(c_793,plain,(
    ! [B_121] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_121),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_121)))) = k5_relat_1(k1_xboole_0,B_121)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_36])).

tff(c_810,plain,(
    ! [B_122] :
      ( k5_relat_1(k1_xboole_0,B_122) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_122))
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22,c_793])).

tff(c_820,plain,(
    ! [B_25] :
      ( k5_relat_1(k1_xboole_0,B_25) = k1_xboole_0
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_810])).

tff(c_860,plain,(
    ! [B_123] :
      ( k5_relat_1(k1_xboole_0,B_123) = k1_xboole_0
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_820])).

tff(c_892,plain,(
    ! [A_125] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_125)) = k1_xboole_0
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_28,c_860])).

tff(c_641,plain,(
    ! [B_109,A_110] :
      ( k5_relat_1(k4_relat_1(B_109),k4_relat_1(A_110)) = k4_relat_1(k5_relat_1(A_110,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_653,plain,(
    ! [A_110] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_110)) = k4_relat_1(k5_relat_1(A_110,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_641])).

tff(c_666,plain,(
    ! [A_110] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_110)) = k4_relat_1(k5_relat_1(A_110,k1_xboole_0))
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_653])).

tff(c_924,plain,(
    ! [A_126] :
      ( k4_relat_1(k5_relat_1(A_126,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_666])).

tff(c_34,plain,(
    ! [A_27] :
      ( k4_relat_1(k4_relat_1(A_27)) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_957,plain,(
    ! [A_126] :
      ( k5_relat_1(A_126,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_126,k1_xboole_0))
      | ~ v1_relat_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_34])).

tff(c_1312,plain,(
    ! [A_135] :
      ( k5_relat_1(A_135,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_135,k1_xboole_0))
      | ~ v1_relat_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_957])).

tff(c_1322,plain,(
    ! [A_24] :
      ( k5_relat_1(A_24,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_30,c_1312])).

tff(c_1328,plain,(
    ! [A_136] :
      ( k5_relat_1(A_136,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1322])).

tff(c_1349,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1328])).

tff(c_1360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_1349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:45:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.79/1.45  
% 2.79/1.45  %Foreground sorts:
% 2.79/1.45  
% 2.79/1.45  
% 2.79/1.45  %Background operators:
% 2.79/1.45  
% 2.79/1.45  
% 2.79/1.45  %Foreground operators:
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.79/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.79/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.79/1.45  
% 3.15/1.47  tff(f_112, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.15/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.47  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.15/1.47  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.15/1.47  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.15/1.47  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.15/1.47  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.47  tff(f_105, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.15/1.47  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.15/1.47  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.15/1.47  tff(f_58, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.15/1.47  tff(f_86, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.15/1.47  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.15/1.47  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.15/1.47  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.15/1.47  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.15/1.47  tff(c_50, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.15/1.47  tff(c_81, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.15/1.47  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.15/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.15/1.47  tff(c_69, plain, (![A_38]: (v1_relat_1(A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.47  tff(c_73, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_69])).
% 3.15/1.47  tff(c_30, plain, (![A_24, B_25]: (v1_relat_1(k5_relat_1(A_24, B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.47  tff(c_6, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.47  tff(c_22, plain, (![B_19]: (k2_zfmisc_1(k1_xboole_0, B_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.47  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.15/1.47  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.47  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.47  tff(c_337, plain, (![A_77, B_78]: (k1_relat_1(k5_relat_1(A_77, B_78))=k1_relat_1(A_77) | ~r1_tarski(k2_relat_1(A_77), k1_relat_1(B_78)) | ~v1_relat_1(B_78) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.15/1.47  tff(c_349, plain, (![B_78]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_78))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_78)) | ~v1_relat_1(B_78) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_337])).
% 3.15/1.47  tff(c_354, plain, (![B_79]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_79))=k1_xboole_0 | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_8, c_48, c_349])).
% 3.15/1.47  tff(c_36, plain, (![A_28]: (k3_xboole_0(A_28, k2_zfmisc_1(k1_relat_1(A_28), k2_relat_1(A_28)))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.15/1.47  tff(c_366, plain, (![B_79]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_79), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_79))))=k5_relat_1(k1_xboole_0, B_79) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_79)) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_354, c_36])).
% 3.15/1.47  tff(c_375, plain, (![B_80]: (k5_relat_1(k1_xboole_0, B_80)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_80)) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_366])).
% 3.15/1.47  tff(c_379, plain, (![B_25]: (k5_relat_1(k1_xboole_0, B_25)=k1_xboole_0 | ~v1_relat_1(B_25) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_375])).
% 3.15/1.47  tff(c_383, plain, (![B_81]: (k5_relat_1(k1_xboole_0, B_81)=k1_xboole_0 | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_379])).
% 3.15/1.47  tff(c_395, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_383])).
% 3.15/1.47  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_395])).
% 3.15/1.47  tff(c_403, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.47  tff(c_28, plain, (![A_23]: (v1_relat_1(k4_relat_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.47  tff(c_478, plain, (![A_90]: (k2_relat_1(k4_relat_1(A_90))=k1_relat_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.47  tff(c_32, plain, (![A_26]: (~v1_xboole_0(k2_relat_1(A_26)) | ~v1_relat_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.47  tff(c_562, plain, (![A_105]: (~v1_xboole_0(k1_relat_1(A_105)) | ~v1_relat_1(k4_relat_1(A_105)) | v1_xboole_0(k4_relat_1(A_105)) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_478, c_32])).
% 3.15/1.47  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.15/1.47  tff(c_574, plain, (![A_106]: (k4_relat_1(A_106)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_106)) | ~v1_relat_1(k4_relat_1(A_106)) | ~v1_relat_1(A_106))), inference(resolution, [status(thm)], [c_562, c_4])).
% 3.15/1.47  tff(c_580, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_574])).
% 3.15/1.47  tff(c_582, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2, c_580])).
% 3.15/1.47  tff(c_583, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_582])).
% 3.15/1.47  tff(c_604, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_583])).
% 3.15/1.47  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_604])).
% 3.15/1.47  tff(c_609, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_582])).
% 3.15/1.47  tff(c_764, plain, (![A_119, B_120]: (k1_relat_1(k5_relat_1(A_119, B_120))=k1_relat_1(A_119) | ~r1_tarski(k2_relat_1(A_119), k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.15/1.47  tff(c_776, plain, (![B_120]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_120))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_764])).
% 3.15/1.47  tff(c_781, plain, (![B_121]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_121))=k1_xboole_0 | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_8, c_48, c_776])).
% 3.15/1.47  tff(c_793, plain, (![B_121]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_121), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_121))))=k5_relat_1(k1_xboole_0, B_121) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_121)) | ~v1_relat_1(B_121))), inference(superposition, [status(thm), theory('equality')], [c_781, c_36])).
% 3.15/1.47  tff(c_810, plain, (![B_122]: (k5_relat_1(k1_xboole_0, B_122)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_122)) | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_793])).
% 3.15/1.47  tff(c_820, plain, (![B_25]: (k5_relat_1(k1_xboole_0, B_25)=k1_xboole_0 | ~v1_relat_1(B_25) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_810])).
% 3.15/1.47  tff(c_860, plain, (![B_123]: (k5_relat_1(k1_xboole_0, B_123)=k1_xboole_0 | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_820])).
% 3.15/1.47  tff(c_892, plain, (![A_125]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_125))=k1_xboole_0 | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_28, c_860])).
% 3.15/1.47  tff(c_641, plain, (![B_109, A_110]: (k5_relat_1(k4_relat_1(B_109), k4_relat_1(A_110))=k4_relat_1(k5_relat_1(A_110, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.47  tff(c_653, plain, (![A_110]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_110))=k4_relat_1(k5_relat_1(A_110, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_609, c_641])).
% 3.15/1.47  tff(c_666, plain, (![A_110]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_110))=k4_relat_1(k5_relat_1(A_110, k1_xboole_0)) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_653])).
% 3.15/1.47  tff(c_924, plain, (![A_126]: (k4_relat_1(k5_relat_1(A_126, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_126) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_892, c_666])).
% 3.15/1.47  tff(c_34, plain, (![A_27]: (k4_relat_1(k4_relat_1(A_27))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.47  tff(c_957, plain, (![A_126]: (k5_relat_1(A_126, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_126, k1_xboole_0)) | ~v1_relat_1(A_126) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_924, c_34])).
% 3.15/1.47  tff(c_1312, plain, (![A_135]: (k5_relat_1(A_135, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_135, k1_xboole_0)) | ~v1_relat_1(A_135) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_957])).
% 3.15/1.47  tff(c_1322, plain, (![A_24]: (k5_relat_1(A_24, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_30, c_1312])).
% 3.15/1.47  tff(c_1328, plain, (![A_136]: (k5_relat_1(A_136, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_136))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1322])).
% 3.15/1.47  tff(c_1349, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1328])).
% 3.15/1.47  tff(c_1360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_1349])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 303
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 3
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 12
% 3.15/1.47  #Demod        : 300
% 3.15/1.47  #Tautology    : 191
% 3.15/1.47  #SimpNegUnit  : 2
% 3.15/1.47  #BackRed      : 2
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.47  Preprocessing        : 0.32
% 3.15/1.47  Parsing              : 0.17
% 3.15/1.47  CNF conversion       : 0.02
% 3.15/1.47  Main loop            : 0.38
% 3.15/1.47  Inferencing          : 0.14
% 3.15/1.47  Reduction            : 0.11
% 3.15/1.47  Demodulation         : 0.08
% 3.15/1.47  BG Simplification    : 0.02
% 3.15/1.47  Subsumption          : 0.07
% 3.15/1.47  Abstraction          : 0.02
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.47  Total                : 0.74
% 3.15/1.47  Index Insertion      : 0.00
% 3.15/1.47  Index Deletion       : 0.00
% 3.15/1.47  Index Matching       : 0.00
% 3.15/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
