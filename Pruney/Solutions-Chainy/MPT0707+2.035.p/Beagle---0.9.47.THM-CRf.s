%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 109 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 127 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(c_24,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_333,plain,(
    ! [B_76,A_77] : k5_relat_1(k6_relat_1(B_76),k6_relat_1(A_77)) = k6_relat_1(k3_xboole_0(A_77,B_76)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_relat_1(A_30),B_31) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_339,plain,(
    ! [A_77,B_76] :
      ( k7_relat_1(k6_relat_1(A_77),B_76) = k6_relat_1(k3_xboole_0(A_77,B_76))
      | ~ v1_relat_1(k6_relat_1(A_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_36])).

tff(c_353,plain,(
    ! [A_78,B_79] : k7_relat_1(k6_relat_1(A_78),B_79) = k6_relat_1(k3_xboole_0(A_78,B_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_339])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( k2_relat_1(k7_relat_1(B_28,A_27)) = k9_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_359,plain,(
    ! [A_78,B_79] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_78,B_79))) = k9_relat_1(k6_relat_1(A_78),B_79)
      | ~ v1_relat_1(k6_relat_1(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_30])).

tff(c_365,plain,(
    ! [A_78,B_79] : k9_relat_1(k6_relat_1(A_78),B_79) = k3_xboole_0(A_78,B_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34,c_359])).

tff(c_40,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_367,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_131,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_131])).

tff(c_32,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [B_9,A_8] : r1_xboole_0(B_9,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_95,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ! [B_9,A_8] : k4_xboole_0(B_9,k4_xboole_0(A_8,B_9)) = B_9 ),
    inference(resolution,[status(thm)],[c_66,c_95])).

tff(c_140,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_140])).

tff(c_389,plain,(
    ! [B_84,A_85] :
      ( k5_relat_1(B_84,k6_relat_1(A_85)) = k8_relat_1(A_85,B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [B_33,A_32] : k5_relat_1(k6_relat_1(B_33),k6_relat_1(A_32)) = k6_relat_1(k3_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_396,plain,(
    ! [A_85,B_33] :
      ( k8_relat_1(A_85,k6_relat_1(B_33)) = k6_relat_1(k3_xboole_0(A_85,B_33))
      | ~ v1_relat_1(k6_relat_1(B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_38])).

tff(c_413,plain,(
    ! [A_85,B_33] : k8_relat_1(A_85,k6_relat_1(B_33)) = k6_relat_1(k3_xboole_0(A_85,B_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_396])).

tff(c_525,plain,(
    ! [B_102,A_103,C_104] :
      ( k8_relat_1(B_102,k8_relat_1(A_103,C_104)) = k8_relat_1(A_103,C_104)
      | ~ r1_tarski(A_103,B_102)
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_540,plain,(
    ! [B_102,A_85,B_33] :
      ( k8_relat_1(B_102,k6_relat_1(k3_xboole_0(A_85,B_33))) = k8_relat_1(A_85,k6_relat_1(B_33))
      | ~ r1_tarski(A_85,B_102)
      | ~ v1_relat_1(k6_relat_1(B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_525])).

tff(c_3446,plain,(
    ! [B_214,A_215,B_216] :
      ( k6_relat_1(k3_xboole_0(B_214,k3_xboole_0(A_215,B_216))) = k6_relat_1(k3_xboole_0(A_215,B_216))
      | ~ r1_tarski(A_215,B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_413,c_413,c_540])).

tff(c_3493,plain,(
    ! [B_214,A_8] :
      ( k6_relat_1(k3_xboole_0(B_214,A_8)) = k6_relat_1(k3_xboole_0(A_8,A_8))
      | ~ r1_tarski(A_8,B_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_3446])).

tff(c_3513,plain,(
    ! [B_217,A_218] :
      ( k6_relat_1(k3_xboole_0(B_217,A_218)) = k6_relat_1(A_218)
      | ~ r1_tarski(A_218,B_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_3493])).

tff(c_3544,plain,(
    ! [B_217,A_218] :
      ( k3_xboole_0(B_217,A_218) = k1_relat_1(k6_relat_1(A_218))
      | ~ r1_tarski(A_218,B_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3513,c_32])).

tff(c_3581,plain,(
    ! [B_219,A_220] :
      ( k3_xboole_0(B_219,A_220) = A_220
      | ~ r1_tarski(A_220,B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3544])).

tff(c_3584,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_139,c_3581])).

tff(c_3588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_3584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.91  
% 4.66/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.91  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.66/1.91  
% 4.66/1.91  %Foreground sorts:
% 4.66/1.91  
% 4.66/1.91  
% 4.66/1.91  %Background operators:
% 4.66/1.91  
% 4.66/1.91  
% 4.66/1.91  %Foreground operators:
% 4.66/1.91  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.66/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/1.91  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.66/1.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.66/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.66/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.66/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.66/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.66/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.66/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.66/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.66/1.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.66/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.66/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.66/1.91  
% 4.66/1.92  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.66/1.92  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.66/1.92  tff(f_79, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.66/1.92  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.66/1.92  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.66/1.92  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 4.66/1.92  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.66/1.92  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.66/1.92  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.66/1.92  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.66/1.92  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/1.92  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 4.66/1.92  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 4.66/1.92  tff(c_24, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.66/1.92  tff(c_34, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.66/1.92  tff(c_333, plain, (![B_76, A_77]: (k5_relat_1(k6_relat_1(B_76), k6_relat_1(A_77))=k6_relat_1(k3_xboole_0(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.66/1.92  tff(c_36, plain, (![A_30, B_31]: (k5_relat_1(k6_relat_1(A_30), B_31)=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.66/1.92  tff(c_339, plain, (![A_77, B_76]: (k7_relat_1(k6_relat_1(A_77), B_76)=k6_relat_1(k3_xboole_0(A_77, B_76)) | ~v1_relat_1(k6_relat_1(A_77)))), inference(superposition, [status(thm), theory('equality')], [c_333, c_36])).
% 4.66/1.92  tff(c_353, plain, (![A_78, B_79]: (k7_relat_1(k6_relat_1(A_78), B_79)=k6_relat_1(k3_xboole_0(A_78, B_79)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_339])).
% 4.66/1.92  tff(c_30, plain, (![B_28, A_27]: (k2_relat_1(k7_relat_1(B_28, A_27))=k9_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.92  tff(c_359, plain, (![A_78, B_79]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_78, B_79)))=k9_relat_1(k6_relat_1(A_78), B_79) | ~v1_relat_1(k6_relat_1(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_353, c_30])).
% 4.66/1.92  tff(c_365, plain, (![A_78, B_79]: (k9_relat_1(k6_relat_1(A_78), B_79)=k3_xboole_0(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34, c_359])).
% 4.66/1.92  tff(c_40, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.92  tff(c_367, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_40])).
% 4.66/1.92  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.92  tff(c_131, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.92  tff(c_139, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_131])).
% 4.66/1.92  tff(c_32, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.66/1.92  tff(c_8, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.92  tff(c_63, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/1.92  tff(c_66, plain, (![B_9, A_8]: (r1_xboole_0(B_9, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_8, c_63])).
% 4.66/1.92  tff(c_95, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.92  tff(c_106, plain, (![B_9, A_8]: (k4_xboole_0(B_9, k4_xboole_0(A_8, B_9))=B_9)), inference(resolution, [status(thm)], [c_66, c_95])).
% 4.66/1.92  tff(c_140, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.92  tff(c_172, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_106, c_140])).
% 4.66/1.92  tff(c_389, plain, (![B_84, A_85]: (k5_relat_1(B_84, k6_relat_1(A_85))=k8_relat_1(A_85, B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.66/1.92  tff(c_38, plain, (![B_33, A_32]: (k5_relat_1(k6_relat_1(B_33), k6_relat_1(A_32))=k6_relat_1(k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.66/1.92  tff(c_396, plain, (![A_85, B_33]: (k8_relat_1(A_85, k6_relat_1(B_33))=k6_relat_1(k3_xboole_0(A_85, B_33)) | ~v1_relat_1(k6_relat_1(B_33)))), inference(superposition, [status(thm), theory('equality')], [c_389, c_38])).
% 4.66/1.92  tff(c_413, plain, (![A_85, B_33]: (k8_relat_1(A_85, k6_relat_1(B_33))=k6_relat_1(k3_xboole_0(A_85, B_33)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_396])).
% 4.66/1.93  tff(c_525, plain, (![B_102, A_103, C_104]: (k8_relat_1(B_102, k8_relat_1(A_103, C_104))=k8_relat_1(A_103, C_104) | ~r1_tarski(A_103, B_102) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.66/1.93  tff(c_540, plain, (![B_102, A_85, B_33]: (k8_relat_1(B_102, k6_relat_1(k3_xboole_0(A_85, B_33)))=k8_relat_1(A_85, k6_relat_1(B_33)) | ~r1_tarski(A_85, B_102) | ~v1_relat_1(k6_relat_1(B_33)))), inference(superposition, [status(thm), theory('equality')], [c_413, c_525])).
% 4.66/1.93  tff(c_3446, plain, (![B_214, A_215, B_216]: (k6_relat_1(k3_xboole_0(B_214, k3_xboole_0(A_215, B_216)))=k6_relat_1(k3_xboole_0(A_215, B_216)) | ~r1_tarski(A_215, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_413, c_413, c_540])).
% 4.66/1.93  tff(c_3493, plain, (![B_214, A_8]: (k6_relat_1(k3_xboole_0(B_214, A_8))=k6_relat_1(k3_xboole_0(A_8, A_8)) | ~r1_tarski(A_8, B_214))), inference(superposition, [status(thm), theory('equality')], [c_172, c_3446])).
% 4.66/1.93  tff(c_3513, plain, (![B_217, A_218]: (k6_relat_1(k3_xboole_0(B_217, A_218))=k6_relat_1(A_218) | ~r1_tarski(A_218, B_217))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_3493])).
% 4.66/1.93  tff(c_3544, plain, (![B_217, A_218]: (k3_xboole_0(B_217, A_218)=k1_relat_1(k6_relat_1(A_218)) | ~r1_tarski(A_218, B_217))), inference(superposition, [status(thm), theory('equality')], [c_3513, c_32])).
% 4.66/1.93  tff(c_3581, plain, (![B_219, A_220]: (k3_xboole_0(B_219, A_220)=A_220 | ~r1_tarski(A_220, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3544])).
% 4.66/1.93  tff(c_3584, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_139, c_3581])).
% 4.66/1.93  tff(c_3588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_3584])).
% 4.66/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.93  
% 4.66/1.93  Inference rules
% 4.66/1.93  ----------------------
% 4.66/1.93  #Ref     : 0
% 4.66/1.93  #Sup     : 920
% 4.66/1.93  #Fact    : 0
% 4.66/1.93  #Define  : 0
% 4.66/1.93  #Split   : 2
% 4.66/1.93  #Chain   : 0
% 4.66/1.93  #Close   : 0
% 4.66/1.93  
% 4.66/1.93  Ordering : KBO
% 4.66/1.93  
% 4.66/1.93  Simplification rules
% 4.66/1.93  ----------------------
% 4.66/1.93  #Subsume      : 129
% 4.66/1.93  #Demod        : 605
% 4.66/1.93  #Tautology    : 341
% 4.66/1.93  #SimpNegUnit  : 1
% 4.66/1.93  #BackRed      : 7
% 4.66/1.93  
% 4.66/1.93  #Partial instantiations: 0
% 4.66/1.93  #Strategies tried      : 1
% 4.66/1.93  
% 4.66/1.93  Timing (in seconds)
% 4.66/1.93  ----------------------
% 4.66/1.93  Preprocessing        : 0.33
% 4.66/1.93  Parsing              : 0.18
% 4.66/1.93  CNF conversion       : 0.02
% 4.66/1.93  Main loop            : 0.80
% 4.66/1.93  Inferencing          : 0.26
% 4.66/1.93  Reduction            : 0.29
% 4.66/1.93  Demodulation         : 0.23
% 4.66/1.93  BG Simplification    : 0.04
% 4.66/1.93  Subsumption          : 0.16
% 4.66/1.93  Abstraction          : 0.04
% 4.66/1.93  MUC search           : 0.00
% 4.66/1.93  Cooper               : 0.00
% 4.66/1.93  Total                : 1.16
% 4.66/1.93  Index Insertion      : 0.00
% 4.66/1.93  Index Deletion       : 0.00
% 4.66/1.93  Index Matching       : 0.00
% 4.66/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
