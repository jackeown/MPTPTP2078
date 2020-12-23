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
% DateTime   : Thu Dec  3 10:07:46 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 123 expanded)
%              Number of equality atoms :   15 (  15 expanded)
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

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_302,plain,(
    ! [A_64,B_65,D_66] :
      ( r2_relset_1(A_64,B_65,D_66,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_305,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_302])).

tff(c_14,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_116,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_116])).

tff(c_147,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_151,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_120,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k2_relat_1(B_40),A_41)
      | ~ v5_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_2])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,'#skF_3')
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_172,plain,(
    ! [B_53] :
      ( r1_tarski(k2_relat_1(B_53),'#skF_3')
      | ~ v5_relat_1(B_53,'#skF_2')
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_120,c_105])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( v5_relat_1(B_12,A_11)
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_182,plain,(
    ! [B_54] :
      ( v5_relat_1(B_54,'#skF_3')
      | ~ v5_relat_1(B_54,'#skF_2')
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_172,c_10])).

tff(c_185,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_182])).

tff(c_188,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_185])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_189,plain,(
    ! [A_55,B_56] :
      ( k8_relat_1(A_55,B_56) = B_56
      | ~ r1_tarski(k2_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_208,plain,(
    ! [A_57,B_58] :
      ( k8_relat_1(A_57,B_58) = B_58
      | ~ v5_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_211,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_188,c_208])).

tff(c_217,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_211])).

tff(c_475,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k6_relset_1(A_81,B_82,C_83,D_84) = k8_relat_1(C_83,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_478,plain,(
    ! [C_83] : k6_relset_1('#skF_1','#skF_2',C_83,'#skF_4') = k8_relat_1(C_83,'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_475])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_479,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_28])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_217,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.34  
% 2.10/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.34  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.34  
% 2.10/1.34  %Foreground sorts:
% 2.10/1.34  
% 2.10/1.34  
% 2.10/1.34  %Background operators:
% 2.10/1.34  
% 2.10/1.34  
% 2.10/1.34  %Foreground operators:
% 2.10/1.34  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.10/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.10/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.34  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.10/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.10/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.10/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.34  
% 2.10/1.36  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.10/1.36  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.10/1.36  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.36  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.36  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.10/1.36  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.10/1.36  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.10/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.10/1.36  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.10/1.36  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.10/1.36  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.10/1.36  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.36  tff(c_302, plain, (![A_64, B_65, D_66]: (r2_relset_1(A_64, B_65, D_66, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.10/1.36  tff(c_305, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_302])).
% 2.10/1.36  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.36  tff(c_113, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.36  tff(c_116, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.10/1.36  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_116])).
% 2.10/1.36  tff(c_147, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.36  tff(c_151, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_147])).
% 2.10/1.36  tff(c_120, plain, (![B_40, A_41]: (r1_tarski(k2_relat_1(B_40), A_41) | ~v5_relat_1(B_40, A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.36  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.36  tff(c_67, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.36  tff(c_71, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_67])).
% 2.10/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.36  tff(c_89, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_71, c_2])).
% 2.10/1.36  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.36  tff(c_105, plain, (![A_3]: (r1_tarski(A_3, '#skF_3') | ~r1_tarski(A_3, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 2.10/1.36  tff(c_172, plain, (![B_53]: (r1_tarski(k2_relat_1(B_53), '#skF_3') | ~v5_relat_1(B_53, '#skF_2') | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_120, c_105])).
% 2.10/1.36  tff(c_10, plain, (![B_12, A_11]: (v5_relat_1(B_12, A_11) | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.36  tff(c_182, plain, (![B_54]: (v5_relat_1(B_54, '#skF_3') | ~v5_relat_1(B_54, '#skF_2') | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_172, c_10])).
% 2.10/1.36  tff(c_185, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_151, c_182])).
% 2.10/1.36  tff(c_188, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_185])).
% 2.10/1.36  tff(c_12, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.36  tff(c_189, plain, (![A_55, B_56]: (k8_relat_1(A_55, B_56)=B_56 | ~r1_tarski(k2_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.36  tff(c_208, plain, (![A_57, B_58]: (k8_relat_1(A_57, B_58)=B_58 | ~v5_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_12, c_189])).
% 2.10/1.36  tff(c_211, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_188, c_208])).
% 2.10/1.36  tff(c_217, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_211])).
% 2.10/1.36  tff(c_475, plain, (![A_81, B_82, C_83, D_84]: (k6_relset_1(A_81, B_82, C_83, D_84)=k8_relat_1(C_83, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.36  tff(c_478, plain, (![C_83]: (k6_relset_1('#skF_1', '#skF_2', C_83, '#skF_4')=k8_relat_1(C_83, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_475])).
% 2.10/1.36  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.36  tff(c_479, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_28])).
% 2.10/1.36  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_217, c_479])).
% 2.10/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.36  
% 2.10/1.36  Inference rules
% 2.10/1.36  ----------------------
% 2.10/1.36  #Ref     : 0
% 2.10/1.36  #Sup     : 115
% 2.10/1.36  #Fact    : 0
% 2.10/1.36  #Define  : 0
% 2.10/1.36  #Split   : 0
% 2.10/1.36  #Chain   : 0
% 2.10/1.36  #Close   : 0
% 2.10/1.36  
% 2.10/1.36  Ordering : KBO
% 2.10/1.36  
% 2.10/1.36  Simplification rules
% 2.10/1.36  ----------------------
% 2.10/1.36  #Subsume      : 23
% 2.10/1.36  #Demod        : 17
% 2.10/1.36  #Tautology    : 39
% 2.10/1.36  #SimpNegUnit  : 0
% 2.10/1.36  #BackRed      : 1
% 2.10/1.36  
% 2.10/1.36  #Partial instantiations: 0
% 2.10/1.36  #Strategies tried      : 1
% 2.10/1.36  
% 2.10/1.36  Timing (in seconds)
% 2.10/1.36  ----------------------
% 2.10/1.36  Preprocessing        : 0.31
% 2.10/1.36  Parsing              : 0.17
% 2.10/1.36  CNF conversion       : 0.02
% 2.10/1.36  Main loop            : 0.25
% 2.10/1.36  Inferencing          : 0.09
% 2.10/1.36  Reduction            : 0.08
% 2.10/1.36  Demodulation         : 0.06
% 2.10/1.36  BG Simplification    : 0.02
% 2.10/1.36  Subsumption          : 0.05
% 2.10/1.36  Abstraction          : 0.01
% 2.10/1.36  MUC search           : 0.00
% 2.10/1.36  Cooper               : 0.00
% 2.10/1.36  Total                : 0.60
% 2.10/1.36  Index Insertion      : 0.00
% 2.10/1.36  Index Deletion       : 0.00
% 2.10/1.36  Index Matching       : 0.00
% 2.10/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
