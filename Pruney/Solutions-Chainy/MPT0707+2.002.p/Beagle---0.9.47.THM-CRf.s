%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   64 (  70 expanded)
%              Number of leaves         :   34 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 (  74 expanded)
%              Number of equality atoms :   29 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_55,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_26,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_relat_1(B_29),k6_relat_1(A_28)) = k6_relat_1(k3_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_478,plain,(
    ! [B_84,A_85] :
      ( k9_relat_1(B_84,k2_relat_1(A_85)) = k2_relat_1(k5_relat_1(A_85,B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_487,plain,(
    ! [A_27,B_84] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_27),B_84)) = k9_relat_1(B_84,A_27)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_478])).

tff(c_597,plain,(
    ! [A_96,B_97] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_96),B_97)) = k9_relat_1(B_97,A_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_487])).

tff(c_609,plain,(
    ! [A_28,B_29] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_28,B_29))) = k9_relat_1(k6_relat_1(A_28),B_29)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_597])).

tff(c_613,plain,(
    ! [A_28,B_29] : k9_relat_1(k6_relat_1(A_28),B_29) = k3_xboole_0(A_28,B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32,c_609])).

tff(c_36,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_614,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_36])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_115,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [B_9,A_8] : r1_xboole_0(B_9,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_308,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_xboole_0(A_66,C_67)
      | ~ r1_xboole_0(B_68,C_67)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_577,plain,(
    ! [A_93,A_94,B_95] :
      ( r1_xboole_0(A_93,k4_xboole_0(A_94,B_95))
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(resolution,[status(thm)],[c_95,c_308])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_924,plain,(
    ! [A_118,A_119,B_120] :
      ( k4_xboole_0(A_118,k4_xboole_0(A_119,B_120)) = A_118
      | ~ r1_tarski(A_118,B_120) ) ),
    inference(resolution,[status(thm)],[c_577,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1047,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = A_121
      | ~ r1_tarski(A_121,B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_4])).

tff(c_1051,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_123,c_1047])).

tff(c_20,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_183,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_195,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,A_19) = k3_xboole_0(A_19,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_183])).

tff(c_1076,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_195])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_1076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:54:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.43  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.78/1.43  
% 2.78/1.44  tff(f_57, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.78/1.44  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.78/1.44  tff(f_70, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.78/1.44  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.78/1.44  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.78/1.44  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.44  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.78/1.44  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.78/1.44  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.78/1.44  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.78/1.44  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.78/1.44  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.78/1.44  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.78/1.44  tff(c_26, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.44  tff(c_32, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.78/1.44  tff(c_34, plain, (![B_29, A_28]: (k5_relat_1(k6_relat_1(B_29), k6_relat_1(A_28))=k6_relat_1(k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.44  tff(c_478, plain, (![B_84, A_85]: (k9_relat_1(B_84, k2_relat_1(A_85))=k2_relat_1(k5_relat_1(A_85, B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.78/1.44  tff(c_487, plain, (![A_27, B_84]: (k2_relat_1(k5_relat_1(k6_relat_1(A_27), B_84))=k9_relat_1(B_84, A_27) | ~v1_relat_1(B_84) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_478])).
% 2.78/1.44  tff(c_597, plain, (![A_96, B_97]: (k2_relat_1(k5_relat_1(k6_relat_1(A_96), B_97))=k9_relat_1(B_97, A_96) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_487])).
% 2.78/1.44  tff(c_609, plain, (![A_28, B_29]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_28, B_29)))=k9_relat_1(k6_relat_1(A_28), B_29) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_597])).
% 2.78/1.44  tff(c_613, plain, (![A_28, B_29]: (k9_relat_1(k6_relat_1(A_28), B_29)=k3_xboole_0(A_28, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32, c_609])).
% 2.78/1.44  tff(c_36, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.44  tff(c_614, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_36])).
% 2.78/1.44  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.44  tff(c_115, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.44  tff(c_123, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_115])).
% 2.78/1.44  tff(c_8, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.44  tff(c_92, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.44  tff(c_95, plain, (![B_9, A_8]: (r1_xboole_0(B_9, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_8, c_92])).
% 2.78/1.44  tff(c_308, plain, (![A_66, C_67, B_68]: (r1_xboole_0(A_66, C_67) | ~r1_xboole_0(B_68, C_67) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.44  tff(c_577, plain, (![A_93, A_94, B_95]: (r1_xboole_0(A_93, k4_xboole_0(A_94, B_95)) | ~r1_tarski(A_93, B_95))), inference(resolution, [status(thm)], [c_95, c_308])).
% 2.78/1.44  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.44  tff(c_924, plain, (![A_118, A_119, B_120]: (k4_xboole_0(A_118, k4_xboole_0(A_119, B_120))=A_118 | ~r1_tarski(A_118, B_120))), inference(resolution, [status(thm)], [c_577, c_10])).
% 2.78/1.44  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.44  tff(c_1047, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=A_121 | ~r1_tarski(A_121, B_122))), inference(superposition, [status(thm), theory('equality')], [c_924, c_4])).
% 2.78/1.44  tff(c_1051, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_123, c_1047])).
% 2.78/1.44  tff(c_20, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.44  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.44  tff(c_137, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.44  tff(c_183, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_14, c_137])).
% 2.78/1.44  tff(c_195, plain, (![B_20, A_19]: (k3_xboole_0(B_20, A_19)=k3_xboole_0(A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_183])).
% 2.78/1.44  tff(c_1076, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1051, c_195])).
% 2.78/1.44  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_614, c_1076])).
% 2.78/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  Inference rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Ref     : 0
% 2.78/1.44  #Sup     : 275
% 2.78/1.44  #Fact    : 0
% 2.78/1.44  #Define  : 0
% 2.78/1.44  #Split   : 0
% 2.78/1.44  #Chain   : 0
% 2.78/1.44  #Close   : 0
% 2.78/1.44  
% 2.78/1.44  Ordering : KBO
% 2.78/1.44  
% 2.78/1.44  Simplification rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Subsume      : 13
% 2.78/1.44  #Demod        : 127
% 2.78/1.44  #Tautology    : 127
% 2.78/1.44  #SimpNegUnit  : 1
% 2.78/1.44  #BackRed      : 3
% 2.78/1.44  
% 2.78/1.44  #Partial instantiations: 0
% 2.78/1.44  #Strategies tried      : 1
% 2.78/1.44  
% 2.78/1.44  Timing (in seconds)
% 2.78/1.44  ----------------------
% 2.78/1.44  Preprocessing        : 0.32
% 2.78/1.44  Parsing              : 0.17
% 2.78/1.44  CNF conversion       : 0.02
% 2.78/1.44  Main loop            : 0.37
% 2.78/1.44  Inferencing          : 0.12
% 2.78/1.44  Reduction            : 0.13
% 2.78/1.44  Demodulation         : 0.11
% 2.78/1.44  BG Simplification    : 0.02
% 2.78/1.44  Subsumption          : 0.06
% 2.78/1.44  Abstraction          : 0.02
% 2.78/1.44  MUC search           : 0.00
% 2.78/1.44  Cooper               : 0.00
% 2.78/1.44  Total                : 0.71
% 2.78/1.44  Index Insertion      : 0.00
% 2.78/1.44  Index Deletion       : 0.00
% 2.78/1.44  Index Matching       : 0.00
% 2.78/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
