%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 356 expanded)
%              Number of leaves         :   31 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          :  144 ( 694 expanded)
%              Number of equality atoms :   49 ( 181 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_91,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [A_9] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_142,plain,(
    ! [A_9] : ~ v1_relat_1(A_9) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_42])).

tff(c_147,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_24,plain,(
    ! [A_16] :
      ( v1_relat_1(k4_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k5_relat_1(A_17,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_223,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_52,B_53)),k2_relat_1(B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_229,plain,(
    ! [A_52] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_52,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_223])).

tff(c_234,plain,(
    ! [A_56] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_56,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_229])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_237,plain,(
    ! [A_56] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_56,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_234,c_4])).

tff(c_240,plain,(
    ! [A_57] :
      ( k2_relat_1(k5_relat_1(A_57,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_237])).

tff(c_30,plain,(
    ! [A_20] :
      ( k3_xboole_0(A_20,k2_zfmisc_1(k1_relat_1(A_20),k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_255,plain,(
    ! [A_57] :
      ( k3_xboole_0(k5_relat_1(A_57,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_57,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_57,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_57,k1_xboole_0))
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_30])).

tff(c_324,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_62,k1_xboole_0))
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14,c_255])).

tff(c_328,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_324])).

tff(c_332,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_328])).

tff(c_347,plain,(
    ! [A_16] :
      ( k5_relat_1(k4_relat_1(A_16),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_332])).

tff(c_28,plain,(
    ! [A_19] :
      ( k4_relat_1(k4_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_264,plain,(
    ! [B_58,A_59] :
      ( k5_relat_1(k4_relat_1(B_58),k4_relat_1(A_59)) = k4_relat_1(k5_relat_1(A_59,B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_956,plain,(
    ! [A_85,B_86] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_85),B_86)) = k5_relat_1(k4_relat_1(B_86),A_85)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(k4_relat_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_264])).

tff(c_1003,plain,(
    ! [A_16] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_16) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_956])).

tff(c_1014,plain,(
    ! [A_87] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_87) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1003])).

tff(c_1032,plain,(
    ! [A_88] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_88) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_24,c_1014])).

tff(c_1066,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_347])).

tff(c_1102,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_147,c_1066])).

tff(c_1031,plain,(
    ! [A_16] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_16) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_1014])).

tff(c_1155,plain,(
    ! [A_89] :
      ( k5_relat_1(k1_xboole_0,A_89) = k1_xboole_0
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_1102,c_1031])).

tff(c_1170,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1155])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1170])).

tff(c_1180,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1218,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1222,plain,(
    ! [A_9] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_1218])).

tff(c_1223,plain,(
    ! [A_9] : ~ v1_relat_1(A_9) ),
    inference(splitLeft,[status(thm)],[c_1222])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1223,c_42])).

tff(c_1229,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1222])).

tff(c_1349,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_113,B_114)),k2_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1405,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_117,B_118)),k2_relat_1(B_118)) = k1_xboole_0
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_1349,c_4])).

tff(c_1423,plain,(
    ! [A_117] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_117,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1405])).

tff(c_1431,plain,(
    ! [A_119] :
      ( k2_relat_1(k5_relat_1(A_119,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_8,c_1423])).

tff(c_1449,plain,(
    ! [A_119] :
      ( k3_xboole_0(k5_relat_1(A_119,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_119,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_119,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_119,k1_xboole_0))
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1431,c_30])).

tff(c_1493,plain,(
    ! [A_123] :
      ( k5_relat_1(A_123,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_123,k1_xboole_0))
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14,c_1449])).

tff(c_1497,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_1493])).

tff(c_1501,plain,(
    ! [A_124] :
      ( k5_relat_1(A_124,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_1497])).

tff(c_1516,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1501])).

tff(c_1524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1180,c_1516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.25/1.52  
% 3.25/1.52  %Foreground sorts:
% 3.25/1.52  
% 3.25/1.52  
% 3.25/1.52  %Background operators:
% 3.25/1.52  
% 3.25/1.52  
% 3.25/1.52  %Foreground operators:
% 3.25/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.52  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.25/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.52  
% 3.25/1.53  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.25/1.53  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.25/1.53  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.25/1.53  tff(f_60, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.25/1.53  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.25/1.53  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.25/1.53  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.25/1.53  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.25/1.53  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.25/1.53  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.25/1.53  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.25/1.53  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.25/1.53  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.25/1.53  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.25/1.53  tff(c_40, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.25/1.53  tff(c_91, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.25/1.53  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.25/1.53  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_118, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.25/1.53  tff(c_122, plain, (![A_9]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_18, c_118])).
% 3.25/1.53  tff(c_142, plain, (![A_9]: (~v1_relat_1(A_9))), inference(splitLeft, [status(thm)], [c_122])).
% 3.25/1.53  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_42])).
% 3.25/1.53  tff(c_147, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_122])).
% 3.25/1.53  tff(c_24, plain, (![A_16]: (v1_relat_1(k4_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.53  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k5_relat_1(A_17, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.25/1.53  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.53  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.53  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.54  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.25/1.54  tff(c_223, plain, (![A_52, B_53]: (r1_tarski(k2_relat_1(k5_relat_1(A_52, B_53)), k2_relat_1(B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.25/1.54  tff(c_229, plain, (![A_52]: (r1_tarski(k2_relat_1(k5_relat_1(A_52, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_36, c_223])).
% 3.25/1.54  tff(c_234, plain, (![A_56]: (r1_tarski(k2_relat_1(k5_relat_1(A_56, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_229])).
% 3.25/1.54  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.54  tff(c_237, plain, (![A_56]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_56, k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_234, c_4])).
% 3.25/1.54  tff(c_240, plain, (![A_57]: (k2_relat_1(k5_relat_1(A_57, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_237])).
% 3.25/1.54  tff(c_30, plain, (![A_20]: (k3_xboole_0(A_20, k2_zfmisc_1(k1_relat_1(A_20), k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.25/1.54  tff(c_255, plain, (![A_57]: (k3_xboole_0(k5_relat_1(A_57, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_57, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_57, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_57, k1_xboole_0)) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_240, c_30])).
% 3.25/1.54  tff(c_324, plain, (![A_62]: (k5_relat_1(A_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_62, k1_xboole_0)) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14, c_255])).
% 3.25/1.54  tff(c_328, plain, (![A_17]: (k5_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_26, c_324])).
% 3.25/1.54  tff(c_332, plain, (![A_63]: (k5_relat_1(A_63, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_328])).
% 3.25/1.54  tff(c_347, plain, (![A_16]: (k5_relat_1(k4_relat_1(A_16), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_24, c_332])).
% 3.25/1.54  tff(c_28, plain, (![A_19]: (k4_relat_1(k4_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.25/1.54  tff(c_264, plain, (![B_58, A_59]: (k5_relat_1(k4_relat_1(B_58), k4_relat_1(A_59))=k4_relat_1(k5_relat_1(A_59, B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.25/1.54  tff(c_956, plain, (![A_85, B_86]: (k4_relat_1(k5_relat_1(k4_relat_1(A_85), B_86))=k5_relat_1(k4_relat_1(B_86), A_85) | ~v1_relat_1(B_86) | ~v1_relat_1(k4_relat_1(A_85)) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_28, c_264])).
% 3.25/1.54  tff(c_1003, plain, (![A_16]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_16)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_16)) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_347, c_956])).
% 3.25/1.54  tff(c_1014, plain, (![A_87]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_87)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_87)) | ~v1_relat_1(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1003])).
% 3.25/1.54  tff(c_1032, plain, (![A_88]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_88)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_24, c_1014])).
% 3.25/1.54  tff(c_1066, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1032, c_347])).
% 3.25/1.54  tff(c_1102, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_147, c_1066])).
% 3.25/1.54  tff(c_1031, plain, (![A_16]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_16)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_24, c_1014])).
% 3.25/1.54  tff(c_1155, plain, (![A_89]: (k5_relat_1(k1_xboole_0, A_89)=k1_xboole_0 | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_1102, c_1031])).
% 3.25/1.54  tff(c_1170, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1155])).
% 3.25/1.54  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_1170])).
% 3.25/1.54  tff(c_1180, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.25/1.54  tff(c_1218, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.25/1.54  tff(c_1222, plain, (![A_9]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_18, c_1218])).
% 3.25/1.54  tff(c_1223, plain, (![A_9]: (~v1_relat_1(A_9))), inference(splitLeft, [status(thm)], [c_1222])).
% 3.25/1.54  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1223, c_42])).
% 3.25/1.54  tff(c_1229, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1222])).
% 3.25/1.54  tff(c_1349, plain, (![A_113, B_114]: (r1_tarski(k2_relat_1(k5_relat_1(A_113, B_114)), k2_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.25/1.54  tff(c_1405, plain, (![A_117, B_118]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_117, B_118)), k2_relat_1(B_118))=k1_xboole_0 | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_1349, c_4])).
% 3.25/1.54  tff(c_1423, plain, (![A_117]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_117, k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1405])).
% 3.25/1.54  tff(c_1431, plain, (![A_119]: (k2_relat_1(k5_relat_1(A_119, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_8, c_1423])).
% 3.25/1.54  tff(c_1449, plain, (![A_119]: (k3_xboole_0(k5_relat_1(A_119, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_119, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_119, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_119, k1_xboole_0)) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_1431, c_30])).
% 3.25/1.54  tff(c_1493, plain, (![A_123]: (k5_relat_1(A_123, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_123, k1_xboole_0)) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14, c_1449])).
% 3.25/1.54  tff(c_1497, plain, (![A_17]: (k5_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_26, c_1493])).
% 3.25/1.54  tff(c_1501, plain, (![A_124]: (k5_relat_1(A_124, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_1497])).
% 3.25/1.54  tff(c_1516, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1501])).
% 3.25/1.54  tff(c_1524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1180, c_1516])).
% 3.25/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.54  
% 3.25/1.54  Inference rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Ref     : 0
% 3.25/1.54  #Sup     : 346
% 3.25/1.54  #Fact    : 0
% 3.25/1.54  #Define  : 0
% 3.25/1.54  #Split   : 5
% 3.25/1.54  #Chain   : 0
% 3.25/1.54  #Close   : 0
% 3.25/1.54  
% 3.25/1.54  Ordering : KBO
% 3.25/1.54  
% 3.25/1.54  Simplification rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Subsume      : 54
% 3.25/1.54  #Demod        : 342
% 3.25/1.54  #Tautology    : 186
% 3.25/1.54  #SimpNegUnit  : 19
% 3.25/1.54  #BackRed      : 7
% 3.25/1.54  
% 3.25/1.54  #Partial instantiations: 0
% 3.25/1.54  #Strategies tried      : 1
% 3.25/1.54  
% 3.25/1.54  Timing (in seconds)
% 3.25/1.54  ----------------------
% 3.25/1.54  Preprocessing        : 0.30
% 3.25/1.54  Parsing              : 0.17
% 3.25/1.54  CNF conversion       : 0.02
% 3.25/1.54  Main loop            : 0.46
% 3.25/1.54  Inferencing          : 0.18
% 3.25/1.54  Reduction            : 0.15
% 3.25/1.54  Demodulation         : 0.11
% 3.25/1.54  BG Simplification    : 0.02
% 3.25/1.54  Subsumption          : 0.08
% 3.25/1.54  Abstraction          : 0.02
% 3.25/1.54  MUC search           : 0.00
% 3.25/1.54  Cooper               : 0.00
% 3.25/1.54  Total                : 0.80
% 3.25/1.54  Index Insertion      : 0.00
% 3.25/1.54  Index Deletion       : 0.00
% 3.25/1.54  Index Matching       : 0.00
% 3.25/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
