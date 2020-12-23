%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:47 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   64 (  84 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 130 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_14,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_114,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_117,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_151,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_155,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_151])).

tff(c_156,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(k2_relat_1(B_51),A_52)
      | ~ v5_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,'#skF_3')
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_4])).

tff(c_170,plain,(
    ! [B_53] :
      ( r1_tarski(k2_relat_1(B_53),'#skF_3')
      | ~ v5_relat_1(B_53,'#skF_2')
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_156,c_103])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( v5_relat_1(B_12,A_11)
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_180,plain,(
    ! [B_54] :
      ( v5_relat_1(B_54,'#skF_3')
      | ~ v5_relat_1(B_54,'#skF_2')
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_170,c_10])).

tff(c_183,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_180])).

tff(c_186,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_183])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_187,plain,(
    ! [A_55,B_56] :
      ( k8_relat_1(A_55,B_56) = B_56
      | ~ r1_tarski(k2_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_206,plain,(
    ! [A_57,B_58] :
      ( k8_relat_1(A_57,B_58) = B_58
      | ~ v5_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_12,c_187])).

tff(c_209,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_186,c_206])).

tff(c_215,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_209])).

tff(c_300,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k6_relset_1(A_64,B_65,C_66,D_67) = k8_relat_1(C_66,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_303,plain,(
    ! [C_66] : k6_relset_1('#skF_1','#skF_2',C_66,'#skF_4') = k8_relat_1(C_66,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_300])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_304,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_26])).

tff(c_305,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_304])).

tff(c_478,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( r2_relset_1(A_81,B_82,C_83,C_83)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_482,plain,(
    ! [C_85] :
      ( r2_relset_1('#skF_1','#skF_2',C_85,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_478])).

tff(c_484,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_482])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.30  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.34/1.30  
% 2.34/1.30  %Foreground sorts:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Background operators:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Foreground operators:
% 2.34/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.34/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.34/1.30  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.34/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.34/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.34/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.30  
% 2.34/1.32  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.34/1.32  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.34/1.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.34/1.32  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.34/1.32  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.34/1.32  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.34/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.34/1.32  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.34/1.32  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.34/1.32  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.34/1.32  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.34/1.32  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.32  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.32  tff(c_111, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.32  tff(c_114, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_111])).
% 2.34/1.32  tff(c_117, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_114])).
% 2.34/1.32  tff(c_151, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.32  tff(c_155, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_151])).
% 2.34/1.32  tff(c_156, plain, (![B_51, A_52]: (r1_tarski(k2_relat_1(B_51), A_52) | ~v5_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.32  tff(c_65, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.32  tff(c_69, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_65])).
% 2.34/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.32  tff(c_87, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_69, c_2])).
% 2.34/1.32  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.32  tff(c_103, plain, (![A_3]: (r1_tarski(A_3, '#skF_3') | ~r1_tarski(A_3, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_4])).
% 2.34/1.32  tff(c_170, plain, (![B_53]: (r1_tarski(k2_relat_1(B_53), '#skF_3') | ~v5_relat_1(B_53, '#skF_2') | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_156, c_103])).
% 2.34/1.32  tff(c_10, plain, (![B_12, A_11]: (v5_relat_1(B_12, A_11) | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_180, plain, (![B_54]: (v5_relat_1(B_54, '#skF_3') | ~v5_relat_1(B_54, '#skF_2') | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_170, c_10])).
% 2.34/1.32  tff(c_183, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_155, c_180])).
% 2.34/1.32  tff(c_186, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_183])).
% 2.34/1.32  tff(c_12, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_187, plain, (![A_55, B_56]: (k8_relat_1(A_55, B_56)=B_56 | ~r1_tarski(k2_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.34/1.32  tff(c_206, plain, (![A_57, B_58]: (k8_relat_1(A_57, B_58)=B_58 | ~v5_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_12, c_187])).
% 2.34/1.32  tff(c_209, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_186, c_206])).
% 2.34/1.32  tff(c_215, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_209])).
% 2.34/1.32  tff(c_300, plain, (![A_64, B_65, C_66, D_67]: (k6_relset_1(A_64, B_65, C_66, D_67)=k8_relat_1(C_66, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.32  tff(c_303, plain, (![C_66]: (k6_relset_1('#skF_1', '#skF_2', C_66, '#skF_4')=k8_relat_1(C_66, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_300])).
% 2.34/1.32  tff(c_26, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.32  tff(c_304, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_26])).
% 2.34/1.32  tff(c_305, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_304])).
% 2.34/1.32  tff(c_478, plain, (![A_81, B_82, C_83, D_84]: (r2_relset_1(A_81, B_82, C_83, C_83) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.32  tff(c_482, plain, (![C_85]: (r2_relset_1('#skF_1', '#skF_2', C_85, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_478])).
% 2.34/1.32  tff(c_484, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_482])).
% 2.34/1.32  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_484])).
% 2.34/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  Inference rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Ref     : 0
% 2.34/1.32  #Sup     : 117
% 2.34/1.32  #Fact    : 0
% 2.34/1.32  #Define  : 0
% 2.34/1.32  #Split   : 0
% 2.34/1.32  #Chain   : 0
% 2.34/1.32  #Close   : 0
% 2.34/1.32  
% 2.34/1.32  Ordering : KBO
% 2.34/1.32  
% 2.34/1.32  Simplification rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Subsume      : 23
% 2.34/1.32  #Demod        : 16
% 2.34/1.32  #Tautology    : 41
% 2.34/1.32  #SimpNegUnit  : 1
% 2.34/1.32  #BackRed      : 1
% 2.34/1.32  
% 2.34/1.32  #Partial instantiations: 0
% 2.34/1.32  #Strategies tried      : 1
% 2.34/1.32  
% 2.34/1.32  Timing (in seconds)
% 2.34/1.32  ----------------------
% 2.34/1.32  Preprocessing        : 0.30
% 2.34/1.32  Parsing              : 0.16
% 2.34/1.32  CNF conversion       : 0.02
% 2.34/1.32  Main loop            : 0.26
% 2.34/1.32  Inferencing          : 0.10
% 2.34/1.32  Reduction            : 0.08
% 2.34/1.32  Demodulation         : 0.06
% 2.34/1.32  BG Simplification    : 0.02
% 2.34/1.32  Subsumption          : 0.05
% 2.34/1.32  Abstraction          : 0.02
% 2.34/1.32  MUC search           : 0.00
% 2.34/1.32  Cooper               : 0.00
% 2.34/1.32  Total                : 0.59
% 2.34/1.32  Index Insertion      : 0.00
% 2.34/1.32  Index Deletion       : 0.00
% 2.34/1.32  Index Matching       : 0.00
% 2.34/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
