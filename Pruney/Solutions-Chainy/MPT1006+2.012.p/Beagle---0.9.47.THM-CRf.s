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
% DateTime   : Thu Dec  3 10:14:04 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 172 expanded)
%              Number of leaves         :   35 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 242 expanded)
%              Number of equality atoms :   23 (  87 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_59,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_68,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_52,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_24,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [B_31] : k2_zfmisc_1(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_30,plain,(
    ! [A_34] : v1_xboole_0('#skF_1'(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_34] : '#skF_1'(A_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_30])).

tff(c_131,plain,(
    ! [B_55,A_56] :
      ( v1_xboole_0(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,(
    ! [B_55] :
      ( v1_xboole_0(B_55)
      | ~ m1_subset_1(B_55,k1_tarski(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_131])).

tff(c_153,plain,(
    ! [B_59] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_134])).

tff(c_162,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_153])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_36,plain,(
    ! [A_39] : k10_relat_1(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [A_39] : k10_relat_1('#skF_4',A_39) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_36])).

tff(c_26,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_33] : m1_subset_1(k1_subset_1(A_33),k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_47,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_179,plain,(
    ! [A_33] : m1_subset_1('#skF_4',k1_zfmisc_1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_47])).

tff(c_299,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k8_relset_1(A_82,B_83,C_84,D_85) = k10_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_302,plain,(
    ! [A_82,B_83,D_85] : k8_relset_1(A_82,B_83,'#skF_4',D_85) = k10_relat_1('#skF_4',D_85) ),
    inference(resolution,[status(thm)],[c_179,c_299])).

tff(c_308,plain,(
    ! [A_82,B_83,D_85] : k8_relset_1(A_82,B_83,'#skF_4',D_85) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_302])).

tff(c_40,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_174,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_40])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.35  
% 1.99/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.35  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.99/1.35  
% 1.99/1.35  %Foreground sorts:
% 1.99/1.35  
% 1.99/1.35  
% 1.99/1.35  %Background operators:
% 1.99/1.35  
% 1.99/1.35  
% 1.99/1.35  %Foreground operators:
% 1.99/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.99/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.99/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.99/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.35  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.35  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.99/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.35  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.35  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.99/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.35  
% 2.24/1.37  tff(f_50, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.24/1.37  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.24/1.37  tff(f_81, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.24/1.37  tff(f_59, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.24/1.37  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.24/1.37  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.24/1.37  tff(f_68, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.24/1.37  tff(f_52, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.24/1.37  tff(f_54, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.24/1.37  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.24/1.37  tff(c_24, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.37  tff(c_22, plain, (![B_31]: (k2_zfmisc_1(k1_xboole_0, B_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.37  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.24/1.37  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42])).
% 2.24/1.37  tff(c_49, plain, (m1_subset_1('#skF_4', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_48])).
% 2.24/1.37  tff(c_30, plain, (![A_34]: (v1_xboole_0('#skF_1'(A_34)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.37  tff(c_59, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.37  tff(c_63, plain, (![A_34]: ('#skF_1'(A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_59])).
% 2.24/1.37  tff(c_64, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_30])).
% 2.24/1.37  tff(c_131, plain, (![B_55, A_56]: (v1_xboole_0(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.37  tff(c_134, plain, (![B_55]: (v1_xboole_0(B_55) | ~m1_subset_1(B_55, k1_tarski(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_131])).
% 2.24/1.37  tff(c_153, plain, (![B_59]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_134])).
% 2.24/1.37  tff(c_162, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_49, c_153])).
% 2.24/1.37  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.37  tff(c_166, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_162, c_2])).
% 2.24/1.37  tff(c_36, plain, (![A_39]: (k10_relat_1(k1_xboole_0, A_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.24/1.37  tff(c_172, plain, (![A_39]: (k10_relat_1('#skF_4', A_39)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_36])).
% 2.24/1.37  tff(c_26, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.24/1.37  tff(c_28, plain, (![A_33]: (m1_subset_1(k1_subset_1(A_33), k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.24/1.37  tff(c_47, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 2.24/1.37  tff(c_179, plain, (![A_33]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_47])).
% 2.24/1.37  tff(c_299, plain, (![A_82, B_83, C_84, D_85]: (k8_relset_1(A_82, B_83, C_84, D_85)=k10_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.37  tff(c_302, plain, (![A_82, B_83, D_85]: (k8_relset_1(A_82, B_83, '#skF_4', D_85)=k10_relat_1('#skF_4', D_85))), inference(resolution, [status(thm)], [c_179, c_299])).
% 2.24/1.37  tff(c_308, plain, (![A_82, B_83, D_85]: (k8_relset_1(A_82, B_83, '#skF_4', D_85)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_302])).
% 2.24/1.37  tff(c_40, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.24/1.37  tff(c_174, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_40])).
% 2.24/1.37  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_308, c_174])).
% 2.24/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.37  
% 2.24/1.37  Inference rules
% 2.24/1.37  ----------------------
% 2.24/1.37  #Ref     : 0
% 2.24/1.37  #Sup     : 60
% 2.24/1.37  #Fact    : 0
% 2.24/1.37  #Define  : 0
% 2.24/1.37  #Split   : 0
% 2.24/1.37  #Chain   : 0
% 2.24/1.37  #Close   : 0
% 2.24/1.37  
% 2.24/1.37  Ordering : KBO
% 2.24/1.37  
% 2.24/1.37  Simplification rules
% 2.24/1.37  ----------------------
% 2.24/1.37  #Subsume      : 1
% 2.24/1.37  #Demod        : 42
% 2.24/1.37  #Tautology    : 54
% 2.24/1.37  #SimpNegUnit  : 0
% 2.24/1.37  #BackRed      : 17
% 2.24/1.37  
% 2.24/1.37  #Partial instantiations: 0
% 2.24/1.37  #Strategies tried      : 1
% 2.24/1.37  
% 2.24/1.37  Timing (in seconds)
% 2.24/1.37  ----------------------
% 2.24/1.37  Preprocessing        : 0.33
% 2.24/1.37  Parsing              : 0.18
% 2.24/1.37  CNF conversion       : 0.02
% 2.24/1.37  Main loop            : 0.16
% 2.24/1.37  Inferencing          : 0.06
% 2.24/1.37  Reduction            : 0.06
% 2.24/1.37  Demodulation         : 0.04
% 2.24/1.37  BG Simplification    : 0.01
% 2.24/1.37  Subsumption          : 0.02
% 2.24/1.37  Abstraction          : 0.01
% 2.24/1.37  MUC search           : 0.00
% 2.24/1.37  Cooper               : 0.00
% 2.24/1.37  Total                : 0.52
% 2.24/1.37  Index Insertion      : 0.00
% 2.24/1.37  Index Deletion       : 0.00
% 2.24/1.37  Index Matching       : 0.00
% 2.24/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
