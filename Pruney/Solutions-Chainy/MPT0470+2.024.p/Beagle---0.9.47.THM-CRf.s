%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 113 expanded)
%              Number of leaves         :   33 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 176 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_44,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_69,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [A_39] :
      ( v1_relat_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(k5_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_43,B_44] :
      ( v1_xboole_0(k2_zfmisc_1(A_43,B_44))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_136,plain,(
    ! [A_52,B_53] :
      ( k2_zfmisc_1(A_52,B_53) = k1_xboole_0
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_145,plain,(
    ! [B_53] : k2_zfmisc_1(k1_xboole_0,B_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_136])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_541,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_80,B_81)),k1_relat_1(A_80))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_546,plain,(
    ! [B_81] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_81)),k1_xboole_0)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_541])).

tff(c_550,plain,(
    ! [B_82] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_82)),k1_xboole_0)
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_546])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_193,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_202,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_560,plain,(
    ! [B_83] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_83)) = k1_xboole_0
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_550,c_202])).

tff(c_34,plain,(
    ! [A_29] :
      ( k3_xboole_0(A_29,k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_575,plain,(
    ! [B_83] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_83),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_83)))) = k5_relat_1(k1_xboole_0,B_83)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_34])).

tff(c_594,plain,(
    ! [B_88] :
      ( k5_relat_1(k1_xboole_0,B_88) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_88))
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_145,c_575])).

tff(c_598,plain,(
    ! [B_28] :
      ( k5_relat_1(k1_xboole_0,B_28) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_594])).

tff(c_602,plain,(
    ! [B_89] :
      ( k5_relat_1(k1_xboole_0,B_89) = k1_xboole_0
      | ~ v1_relat_1(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_598])).

tff(c_617,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_602])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_617])).

tff(c_626,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_648,plain,(
    ! [A_93,B_94] :
      ( v1_xboole_0(k2_zfmisc_1(A_93,B_94))
      | ~ v1_xboole_0(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_703,plain,(
    ! [A_104,B_105] :
      ( k2_zfmisc_1(A_104,B_105) = k1_xboole_0
      | ~ v1_xboole_0(B_105) ) ),
    inference(resolution,[status(thm)],[c_648,c_4])).

tff(c_712,plain,(
    ! [A_104] : k2_zfmisc_1(A_104,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_703])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1287,plain,(
    ! [A_142,B_143] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_142,B_143)),k2_relat_1(B_143))
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1301,plain,(
    ! [A_142] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_142,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1287])).

tff(c_1311,plain,(
    ! [A_144] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_144,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1301])).

tff(c_755,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_764,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_755])).

tff(c_1326,plain,(
    ! [A_145] :
      ( k2_relat_1(k5_relat_1(A_145,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_1311,c_764])).

tff(c_1341,plain,(
    ! [A_145] :
      ( k3_xboole_0(k5_relat_1(A_145,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_145,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_145,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_145,k1_xboole_0))
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_34])).

tff(c_1421,plain,(
    ! [A_148] :
      ( k5_relat_1(A_148,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_148,k1_xboole_0))
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_712,c_1341])).

tff(c_1428,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_1421])).

tff(c_1443,plain,(
    ! [A_154] :
      ( k5_relat_1(A_154,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1428])).

tff(c_1458,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1443])).

tff(c_1467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_1458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  
% 3.09/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.48  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.17/1.48  
% 3.17/1.48  %Foreground sorts:
% 3.17/1.48  
% 3.17/1.48  
% 3.17/1.48  %Background operators:
% 3.17/1.48  
% 3.17/1.48  
% 3.17/1.48  %Foreground operators:
% 3.17/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.17/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.17/1.48  
% 3.17/1.50  tff(f_96, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.17/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.17/1.50  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.17/1.50  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.17/1.50  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.17/1.50  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.17/1.50  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.17/1.50  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.17/1.50  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.17/1.50  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.17/1.50  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.50  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.17/1.50  tff(f_52, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.17/1.50  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.17/1.50  tff(c_44, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.17/1.50  tff(c_69, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.17/1.50  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.17/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.17/1.50  tff(c_64, plain, (![A_39]: (v1_relat_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.50  tff(c_68, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_64])).
% 3.17/1.50  tff(c_32, plain, (![A_27, B_28]: (v1_relat_1(k5_relat_1(A_27, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.17/1.50  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.50  tff(c_86, plain, (![A_43, B_44]: (v1_xboole_0(k2_zfmisc_1(A_43, B_44)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.50  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.17/1.50  tff(c_136, plain, (![A_52, B_53]: (k2_zfmisc_1(A_52, B_53)=k1_xboole_0 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_86, c_4])).
% 3.17/1.50  tff(c_145, plain, (![B_53]: (k2_zfmisc_1(k1_xboole_0, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_136])).
% 3.17/1.50  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.17/1.50  tff(c_541, plain, (![A_80, B_81]: (r1_tarski(k1_relat_1(k5_relat_1(A_80, B_81)), k1_relat_1(A_80)) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.17/1.50  tff(c_546, plain, (![B_81]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_81)), k1_xboole_0) | ~v1_relat_1(B_81) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_541])).
% 3.17/1.50  tff(c_550, plain, (![B_82]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_82)), k1_xboole_0) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_546])).
% 3.17/1.50  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.50  tff(c_193, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.50  tff(c_202, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_193])).
% 3.17/1.50  tff(c_560, plain, (![B_83]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_83))=k1_xboole_0 | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_550, c_202])).
% 3.17/1.50  tff(c_34, plain, (![A_29]: (k3_xboole_0(A_29, k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.17/1.50  tff(c_575, plain, (![B_83]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_83), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_83))))=k5_relat_1(k1_xboole_0, B_83) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_83)) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_560, c_34])).
% 3.17/1.50  tff(c_594, plain, (![B_88]: (k5_relat_1(k1_xboole_0, B_88)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_88)) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_145, c_575])).
% 3.17/1.50  tff(c_598, plain, (![B_28]: (k5_relat_1(k1_xboole_0, B_28)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_594])).
% 3.17/1.50  tff(c_602, plain, (![B_89]: (k5_relat_1(k1_xboole_0, B_89)=k1_xboole_0 | ~v1_relat_1(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_598])).
% 3.17/1.50  tff(c_617, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_602])).
% 3.17/1.50  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_617])).
% 3.17/1.50  tff(c_626, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.17/1.50  tff(c_648, plain, (![A_93, B_94]: (v1_xboole_0(k2_zfmisc_1(A_93, B_94)) | ~v1_xboole_0(B_94))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.17/1.50  tff(c_703, plain, (![A_104, B_105]: (k2_zfmisc_1(A_104, B_105)=k1_xboole_0 | ~v1_xboole_0(B_105))), inference(resolution, [status(thm)], [c_648, c_4])).
% 3.17/1.50  tff(c_712, plain, (![A_104]: (k2_zfmisc_1(A_104, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_703])).
% 3.17/1.50  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.17/1.50  tff(c_1287, plain, (![A_142, B_143]: (r1_tarski(k2_relat_1(k5_relat_1(A_142, B_143)), k2_relat_1(B_143)) | ~v1_relat_1(B_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.50  tff(c_1301, plain, (![A_142]: (r1_tarski(k2_relat_1(k5_relat_1(A_142, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1287])).
% 3.17/1.50  tff(c_1311, plain, (![A_144]: (r1_tarski(k2_relat_1(k5_relat_1(A_144, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1301])).
% 3.17/1.50  tff(c_755, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.50  tff(c_764, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_755])).
% 3.17/1.50  tff(c_1326, plain, (![A_145]: (k2_relat_1(k5_relat_1(A_145, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_1311, c_764])).
% 3.17/1.50  tff(c_1341, plain, (![A_145]: (k3_xboole_0(k5_relat_1(A_145, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_145, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_145, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_145, k1_xboole_0)) | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_1326, c_34])).
% 3.17/1.50  tff(c_1421, plain, (![A_148]: (k5_relat_1(A_148, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_148, k1_xboole_0)) | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_712, c_1341])).
% 3.17/1.50  tff(c_1428, plain, (![A_27]: (k5_relat_1(A_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_32, c_1421])).
% 3.17/1.50  tff(c_1443, plain, (![A_154]: (k5_relat_1(A_154, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1428])).
% 3.17/1.50  tff(c_1458, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1443])).
% 3.17/1.50  tff(c_1467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_626, c_1458])).
% 3.17/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.50  
% 3.17/1.50  Inference rules
% 3.17/1.50  ----------------------
% 3.17/1.50  #Ref     : 0
% 3.17/1.50  #Sup     : 330
% 3.17/1.50  #Fact    : 0
% 3.17/1.50  #Define  : 0
% 3.17/1.50  #Split   : 1
% 3.17/1.50  #Chain   : 0
% 3.17/1.50  #Close   : 0
% 3.17/1.50  
% 3.17/1.50  Ordering : KBO
% 3.17/1.50  
% 3.17/1.50  Simplification rules
% 3.17/1.50  ----------------------
% 3.17/1.50  #Subsume      : 6
% 3.17/1.50  #Demod        : 251
% 3.17/1.50  #Tautology    : 274
% 3.17/1.50  #SimpNegUnit  : 2
% 3.17/1.50  #BackRed      : 0
% 3.17/1.50  
% 3.17/1.50  #Partial instantiations: 0
% 3.17/1.50  #Strategies tried      : 1
% 3.17/1.50  
% 3.17/1.50  Timing (in seconds)
% 3.17/1.50  ----------------------
% 3.17/1.50  Preprocessing        : 0.33
% 3.17/1.50  Parsing              : 0.18
% 3.17/1.50  CNF conversion       : 0.02
% 3.17/1.50  Main loop            : 0.39
% 3.17/1.50  Inferencing          : 0.15
% 3.17/1.50  Reduction            : 0.12
% 3.17/1.50  Demodulation         : 0.08
% 3.17/1.50  BG Simplification    : 0.02
% 3.17/1.50  Subsumption          : 0.07
% 3.17/1.50  Abstraction          : 0.02
% 3.17/1.50  MUC search           : 0.00
% 3.17/1.50  Cooper               : 0.00
% 3.17/1.50  Total                : 0.75
% 3.17/1.50  Index Insertion      : 0.00
% 3.17/1.50  Index Deletion       : 0.00
% 3.17/1.50  Index Matching       : 0.00
% 3.17/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
