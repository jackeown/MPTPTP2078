%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 109 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_74,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_49,axiom,(
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

tff(c_28,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k7_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [B_26,A_25] : k5_relat_1(k6_relat_1(B_26),k6_relat_1(A_25)) = k6_relat_1(k3_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_249,plain,(
    ! [A_25,A_57] :
      ( k7_relat_1(k6_relat_1(A_25),A_57) = k6_relat_1(k3_xboole_0(A_25,A_57))
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_34])).

tff(c_262,plain,(
    ! [A_59,A_60] : k7_relat_1(k6_relat_1(A_59),A_60) = k6_relat_1(k3_xboole_0(A_59,A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_249])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [A_59,A_60] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_59,A_60))) = k9_relat_1(k6_relat_1(A_59),A_60)
      | ~ v1_relat_1(k6_relat_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_16])).

tff(c_281,plain,(
    ! [A_59,A_60] : k9_relat_1(k6_relat_1(A_59),A_60) = k3_xboole_0(A_59,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_272])).

tff(c_36,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_363,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_36])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_103])).

tff(c_22,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_258,plain,(
    ! [A_25,A_57] : k7_relat_1(k6_relat_1(A_25),A_57) = k6_relat_1(k3_xboole_0(A_25,A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_249])).

tff(c_30,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_283,plain,(
    ! [C_61,B_62,A_63] :
      ( v4_relat_1(C_61,B_62)
      | ~ v4_relat_1(C_61,A_63)
      | ~ v1_relat_1(C_61)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_285,plain,(
    ! [A_24,B_62] :
      ( v4_relat_1(k6_relat_1(A_24),B_62)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ r1_tarski(A_24,B_62) ) ),
    inference(resolution,[status(thm)],[c_30,c_283])).

tff(c_351,plain,(
    ! [A_66,B_67] :
      ( v4_relat_1(k6_relat_1(A_66),B_67)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_285])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_356,plain,(
    ! [A_66,B_67] :
      ( k7_relat_1(k6_relat_1(A_66),B_67) = k6_relat_1(A_66)
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_351,c_18])).

tff(c_384,plain,(
    ! [A_70,B_71] :
      ( k6_relat_1(k3_xboole_0(A_70,B_71)) = k6_relat_1(A_70)
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_258,c_356])).

tff(c_417,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = k1_relat_1(k6_relat_1(A_70))
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_22])).

tff(c_450,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_417])).

tff(c_454,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_450])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_461,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_134])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.40  
% 2.34/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.41  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.34/1.41  
% 2.34/1.41  %Foreground sorts:
% 2.34/1.41  
% 2.34/1.41  
% 2.34/1.41  %Background operators:
% 2.34/1.41  
% 2.34/1.41  
% 2.34/1.41  %Foreground operators:
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.34/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.34/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.34/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.34/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.34/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.34/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.41  
% 2.34/1.42  tff(f_72, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.34/1.42  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.34/1.42  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.34/1.42  tff(f_74, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.34/1.42  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.34/1.42  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.34/1.42  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.34/1.42  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.34/1.42  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.34/1.42  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.34/1.42  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.34/1.42  tff(c_28, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.42  tff(c_24, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.42  tff(c_242, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k7_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.42  tff(c_34, plain, (![B_26, A_25]: (k5_relat_1(k6_relat_1(B_26), k6_relat_1(A_25))=k6_relat_1(k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.42  tff(c_249, plain, (![A_25, A_57]: (k7_relat_1(k6_relat_1(A_25), A_57)=k6_relat_1(k3_xboole_0(A_25, A_57)) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_34])).
% 2.34/1.42  tff(c_262, plain, (![A_59, A_60]: (k7_relat_1(k6_relat_1(A_59), A_60)=k6_relat_1(k3_xboole_0(A_59, A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_249])).
% 2.34/1.42  tff(c_16, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.42  tff(c_272, plain, (![A_59, A_60]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_59, A_60)))=k9_relat_1(k6_relat_1(A_59), A_60) | ~v1_relat_1(k6_relat_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_262, c_16])).
% 2.34/1.42  tff(c_281, plain, (![A_59, A_60]: (k9_relat_1(k6_relat_1(A_59), A_60)=k3_xboole_0(A_59, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_272])).
% 2.34/1.42  tff(c_36, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.42  tff(c_363, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_36])).
% 2.34/1.42  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.42  tff(c_103, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.42  tff(c_107, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_103])).
% 2.34/1.42  tff(c_22, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.42  tff(c_258, plain, (![A_25, A_57]: (k7_relat_1(k6_relat_1(A_25), A_57)=k6_relat_1(k3_xboole_0(A_25, A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_249])).
% 2.34/1.42  tff(c_30, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.42  tff(c_283, plain, (![C_61, B_62, A_63]: (v4_relat_1(C_61, B_62) | ~v4_relat_1(C_61, A_63) | ~v1_relat_1(C_61) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.34/1.42  tff(c_285, plain, (![A_24, B_62]: (v4_relat_1(k6_relat_1(A_24), B_62) | ~v1_relat_1(k6_relat_1(A_24)) | ~r1_tarski(A_24, B_62))), inference(resolution, [status(thm)], [c_30, c_283])).
% 2.34/1.42  tff(c_351, plain, (![A_66, B_67]: (v4_relat_1(k6_relat_1(A_66), B_67) | ~r1_tarski(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_285])).
% 2.34/1.42  tff(c_18, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.34/1.42  tff(c_356, plain, (![A_66, B_67]: (k7_relat_1(k6_relat_1(A_66), B_67)=k6_relat_1(A_66) | ~v1_relat_1(k6_relat_1(A_66)) | ~r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_351, c_18])).
% 2.34/1.42  tff(c_384, plain, (![A_70, B_71]: (k6_relat_1(k3_xboole_0(A_70, B_71))=k6_relat_1(A_70) | ~r1_tarski(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_258, c_356])).
% 2.34/1.42  tff(c_417, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=k1_relat_1(k6_relat_1(A_70)) | ~r1_tarski(A_70, B_71))), inference(superposition, [status(thm), theory('equality')], [c_384, c_22])).
% 2.34/1.42  tff(c_450, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_417])).
% 2.34/1.42  tff(c_454, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_107, c_450])).
% 2.34/1.42  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.42  tff(c_113, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.42  tff(c_128, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 2.34/1.42  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.42  tff(c_134, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 2.34/1.42  tff(c_461, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_454, c_134])).
% 2.34/1.42  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_461])).
% 2.34/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.42  
% 2.34/1.42  Inference rules
% 2.34/1.42  ----------------------
% 2.34/1.42  #Ref     : 0
% 2.34/1.42  #Sup     : 103
% 2.34/1.42  #Fact    : 0
% 2.34/1.42  #Define  : 0
% 2.34/1.42  #Split   : 0
% 2.34/1.42  #Chain   : 0
% 2.34/1.42  #Close   : 0
% 2.34/1.42  
% 2.34/1.42  Ordering : KBO
% 2.34/1.42  
% 2.34/1.42  Simplification rules
% 2.34/1.42  ----------------------
% 2.34/1.42  #Subsume      : 1
% 2.34/1.42  #Demod        : 45
% 2.34/1.42  #Tautology    : 67
% 2.34/1.42  #SimpNegUnit  : 1
% 2.34/1.42  #BackRed      : 1
% 2.34/1.42  
% 2.34/1.42  #Partial instantiations: 0
% 2.34/1.42  #Strategies tried      : 1
% 2.34/1.42  
% 2.34/1.42  Timing (in seconds)
% 2.34/1.42  ----------------------
% 2.34/1.42  Preprocessing        : 0.37
% 2.34/1.42  Parsing              : 0.20
% 2.34/1.42  CNF conversion       : 0.02
% 2.34/1.42  Main loop            : 0.22
% 2.34/1.42  Inferencing          : 0.08
% 2.34/1.42  Reduction            : 0.08
% 2.34/1.42  Demodulation         : 0.06
% 2.34/1.42  BG Simplification    : 0.01
% 2.34/1.42  Subsumption          : 0.03
% 2.34/1.42  Abstraction          : 0.02
% 2.34/1.42  MUC search           : 0.00
% 2.34/1.42  Cooper               : 0.00
% 2.34/1.42  Total                : 0.62
% 2.34/1.42  Index Insertion      : 0.00
% 2.34/1.42  Index Deletion       : 0.00
% 2.34/1.42  Index Matching       : 0.00
% 2.34/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
