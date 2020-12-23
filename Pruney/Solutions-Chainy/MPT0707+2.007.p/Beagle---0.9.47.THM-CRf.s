%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:17 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   68 (  86 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_76,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_32,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    ! [A_55,B_56] :
      ( k5_relat_1(k6_relat_1(A_55),B_56) = k7_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [B_26,A_25] : k5_relat_1(k6_relat_1(B_26),k6_relat_1(A_25)) = k6_relat_1(k3_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_243,plain,(
    ! [A_25,A_55] :
      ( k7_relat_1(k6_relat_1(A_25),A_55) = k6_relat_1(k3_xboole_0(A_25,A_55))
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_36])).

tff(c_256,plain,(
    ! [A_57,A_58] : k7_relat_1(k6_relat_1(A_57),A_58) = k6_relat_1(k3_xboole_0(A_57,A_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_262,plain,(
    ! [A_57,A_58] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_57,A_58))) = k9_relat_1(k6_relat_1(A_57),A_58)
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_14])).

tff(c_275,plain,(
    ! [A_57,A_58] : k9_relat_1(k6_relat_1(A_57),A_58) = k3_xboole_0(A_57,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_262])).

tff(c_38,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_369,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_122,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_20,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_252,plain,(
    ! [A_25,A_55] : k7_relat_1(k6_relat_1(A_25),A_55) = k6_relat_1(k3_xboole_0(A_25,A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_28,plain,(
    ! [A_23] : v4_relat_1(k6_relat_1(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_348,plain,(
    ! [C_64,B_65,A_66] :
      ( v4_relat_1(C_64,B_65)
      | ~ v4_relat_1(C_64,A_66)
      | ~ v1_relat_1(C_64)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_350,plain,(
    ! [A_23,B_65] :
      ( v4_relat_1(k6_relat_1(A_23),B_65)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_23,B_65) ) ),
    inference(resolution,[status(thm)],[c_28,c_348])).

tff(c_357,plain,(
    ! [A_67,B_68] :
      ( v4_relat_1(k6_relat_1(A_67),B_68)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_350])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_362,plain,(
    ! [A_67,B_68] :
      ( k7_relat_1(k6_relat_1(A_67),B_68) = k6_relat_1(A_67)
      | ~ v1_relat_1(k6_relat_1(A_67))
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_357,c_16])).

tff(c_390,plain,(
    ! [A_71,B_72] :
      ( k6_relat_1(k3_xboole_0(A_71,B_72)) = k6_relat_1(A_71)
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_252,c_362])).

tff(c_426,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = k1_relat_1(k6_relat_1(A_71))
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_20])).

tff(c_473,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_426])).

tff(c_477,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_130,c_473])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(B_44,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_137,plain,(
    ! [B_44,A_43] : k3_xboole_0(B_44,A_43) = k3_xboole_0(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_8])).

tff(c_487,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_137])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.51/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.51/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.38  
% 2.51/1.40  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.51/1.40  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.51/1.40  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.51/1.40  tff(f_76, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.51/1.40  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.51/1.40  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.51/1.40  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.51/1.40  tff(f_70, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.51/1.40  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.51/1.40  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.51/1.40  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.51/1.40  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.51/1.40  tff(c_32, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.51/1.40  tff(c_22, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.40  tff(c_236, plain, (![A_55, B_56]: (k5_relat_1(k6_relat_1(A_55), B_56)=k7_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.40  tff(c_36, plain, (![B_26, A_25]: (k5_relat_1(k6_relat_1(B_26), k6_relat_1(A_25))=k6_relat_1(k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.40  tff(c_243, plain, (![A_25, A_55]: (k7_relat_1(k6_relat_1(A_25), A_55)=k6_relat_1(k3_xboole_0(A_25, A_55)) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_236, c_36])).
% 2.51/1.40  tff(c_256, plain, (![A_57, A_58]: (k7_relat_1(k6_relat_1(A_57), A_58)=k6_relat_1(k3_xboole_0(A_57, A_58)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_243])).
% 2.51/1.40  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.40  tff(c_262, plain, (![A_57, A_58]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_57, A_58)))=k9_relat_1(k6_relat_1(A_57), A_58) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_14])).
% 2.51/1.40  tff(c_275, plain, (![A_57, A_58]: (k9_relat_1(k6_relat_1(A_57), A_58)=k3_xboole_0(A_57, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_262])).
% 2.51/1.40  tff(c_38, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.51/1.40  tff(c_369, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_38])).
% 2.51/1.40  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.51/1.40  tff(c_122, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.40  tff(c_130, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_122])).
% 2.51/1.40  tff(c_20, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.40  tff(c_252, plain, (![A_25, A_55]: (k7_relat_1(k6_relat_1(A_25), A_55)=k6_relat_1(k3_xboole_0(A_25, A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_243])).
% 2.51/1.40  tff(c_28, plain, (![A_23]: (v4_relat_1(k6_relat_1(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.40  tff(c_348, plain, (![C_64, B_65, A_66]: (v4_relat_1(C_64, B_65) | ~v4_relat_1(C_64, A_66) | ~v1_relat_1(C_64) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.40  tff(c_350, plain, (![A_23, B_65]: (v4_relat_1(k6_relat_1(A_23), B_65) | ~v1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_23, B_65))), inference(resolution, [status(thm)], [c_28, c_348])).
% 2.51/1.40  tff(c_357, plain, (![A_67, B_68]: (v4_relat_1(k6_relat_1(A_67), B_68) | ~r1_tarski(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_350])).
% 2.51/1.40  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.40  tff(c_362, plain, (![A_67, B_68]: (k7_relat_1(k6_relat_1(A_67), B_68)=k6_relat_1(A_67) | ~v1_relat_1(k6_relat_1(A_67)) | ~r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_357, c_16])).
% 2.51/1.40  tff(c_390, plain, (![A_71, B_72]: (k6_relat_1(k3_xboole_0(A_71, B_72))=k6_relat_1(A_71) | ~r1_tarski(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_252, c_362])).
% 2.51/1.40  tff(c_426, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=k1_relat_1(k6_relat_1(A_71)) | ~r1_tarski(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_390, c_20])).
% 2.51/1.40  tff(c_473, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_426])).
% 2.51/1.40  tff(c_477, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_130, c_473])).
% 2.51/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.40  tff(c_97, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.40  tff(c_131, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(B_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 2.51/1.40  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.40  tff(c_137, plain, (![B_44, A_43]: (k3_xboole_0(B_44, A_43)=k3_xboole_0(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_131, c_8])).
% 2.51/1.40  tff(c_487, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_477, c_137])).
% 2.51/1.40  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_487])).
% 2.51/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.40  
% 2.51/1.40  Inference rules
% 2.51/1.40  ----------------------
% 2.51/1.40  #Ref     : 0
% 2.51/1.40  #Sup     : 110
% 2.51/1.40  #Fact    : 0
% 2.51/1.40  #Define  : 0
% 2.51/1.40  #Split   : 0
% 2.51/1.40  #Chain   : 0
% 2.51/1.40  #Close   : 0
% 2.51/1.40  
% 2.51/1.40  Ordering : KBO
% 2.51/1.40  
% 2.51/1.40  Simplification rules
% 2.51/1.40  ----------------------
% 2.51/1.40  #Subsume      : 1
% 2.51/1.40  #Demod        : 50
% 2.51/1.40  #Tautology    : 71
% 2.51/1.40  #SimpNegUnit  : 1
% 2.51/1.40  #BackRed      : 1
% 2.51/1.40  
% 2.51/1.40  #Partial instantiations: 0
% 2.51/1.40  #Strategies tried      : 1
% 2.51/1.40  
% 2.51/1.40  Timing (in seconds)
% 2.51/1.40  ----------------------
% 2.51/1.40  Preprocessing        : 0.34
% 2.51/1.40  Parsing              : 0.18
% 2.51/1.40  CNF conversion       : 0.02
% 2.51/1.40  Main loop            : 0.23
% 2.51/1.40  Inferencing          : 0.09
% 2.51/1.40  Reduction            : 0.09
% 2.51/1.40  Demodulation         : 0.07
% 2.51/1.40  BG Simplification    : 0.02
% 2.51/1.40  Subsumption          : 0.03
% 2.51/1.40  Abstraction          : 0.02
% 2.51/1.40  MUC search           : 0.00
% 2.51/1.40  Cooper               : 0.00
% 2.51/1.40  Total                : 0.60
% 2.51/1.40  Index Insertion      : 0.00
% 2.51/1.40  Index Deletion       : 0.00
% 2.51/1.40  Index Matching       : 0.00
% 2.51/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
