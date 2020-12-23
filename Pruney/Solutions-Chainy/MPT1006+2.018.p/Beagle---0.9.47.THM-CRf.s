%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:05 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 169 expanded)
%              Number of leaves         :   34 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 239 expanded)
%              Number of equality atoms :   21 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_72,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_24,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [B_31] : k2_zfmisc_1(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_47])).

tff(c_26,plain,(
    ! [A_32] : v1_xboole_0('#skF_1'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_32] : '#skF_1'(A_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_51])).

tff(c_63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_134,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [B_58] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_tarski(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_154,plain,(
    ! [B_63] :
      ( v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_137])).

tff(c_163,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_154])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_167,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_36,plain,(
    ! [A_41] : k10_relat_1(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    ! [A_41] : k10_relat_1('#skF_4',A_41) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_36])).

tff(c_30,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_181,plain,(
    ! [A_34] : m1_subset_1('#skF_4',k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_30])).

tff(c_294,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k8_relset_1(A_89,B_90,C_91,D_92) = k10_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_301,plain,(
    ! [A_89,B_90,D_92] : k8_relset_1(A_89,B_90,'#skF_4',D_92) = k10_relat_1('#skF_4',D_92) ),
    inference(resolution,[status(thm)],[c_181,c_294])).

tff(c_305,plain,(
    ! [A_89,B_90,D_92] : k8_relset_1(A_89,B_90,'#skF_4',D_92) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_301])).

tff(c_40,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_174,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_40])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.07/1.32  
% 2.07/1.32  %Foreground sorts:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Background operators:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Foreground operators:
% 2.07/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.32  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.07/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.07/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.32  
% 2.07/1.33  tff(f_50, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.07/1.33  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.07/1.33  tff(f_85, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.07/1.33  tff(f_55, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.07/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.07/1.33  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.07/1.33  tff(f_72, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.07/1.33  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.07/1.33  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.07/1.33  tff(c_24, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.33  tff(c_22, plain, (![B_31]: (k2_zfmisc_1(k1_xboole_0, B_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.07/1.33  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.33  tff(c_47, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42])).
% 2.07/1.33  tff(c_48, plain, (m1_subset_1('#skF_4', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_47])).
% 2.07/1.33  tff(c_26, plain, (![A_32]: (v1_xboole_0('#skF_1'(A_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.33  tff(c_51, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.33  tff(c_55, plain, (![A_32]: ('#skF_1'(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_51])).
% 2.07/1.33  tff(c_63, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_26])).
% 2.07/1.33  tff(c_134, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.33  tff(c_137, plain, (![B_58]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_tarski(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_134])).
% 2.07/1.33  tff(c_154, plain, (![B_63]: (v1_xboole_0(B_63) | ~m1_subset_1(B_63, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_137])).
% 2.07/1.33  tff(c_163, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_154])).
% 2.07/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.33  tff(c_167, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_163, c_2])).
% 2.07/1.33  tff(c_36, plain, (![A_41]: (k10_relat_1(k1_xboole_0, A_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.33  tff(c_178, plain, (![A_41]: (k10_relat_1('#skF_4', A_41)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_36])).
% 2.07/1.33  tff(c_30, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.33  tff(c_181, plain, (![A_34]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_30])).
% 2.07/1.33  tff(c_294, plain, (![A_89, B_90, C_91, D_92]: (k8_relset_1(A_89, B_90, C_91, D_92)=k10_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.33  tff(c_301, plain, (![A_89, B_90, D_92]: (k8_relset_1(A_89, B_90, '#skF_4', D_92)=k10_relat_1('#skF_4', D_92))), inference(resolution, [status(thm)], [c_181, c_294])).
% 2.07/1.33  tff(c_305, plain, (![A_89, B_90, D_92]: (k8_relset_1(A_89, B_90, '#skF_4', D_92)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_301])).
% 2.07/1.33  tff(c_40, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.33  tff(c_174, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_40])).
% 2.07/1.33  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_174])).
% 2.07/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.33  
% 2.07/1.33  Inference rules
% 2.07/1.33  ----------------------
% 2.07/1.33  #Ref     : 0
% 2.07/1.33  #Sup     : 59
% 2.07/1.33  #Fact    : 0
% 2.07/1.33  #Define  : 0
% 2.07/1.33  #Split   : 0
% 2.07/1.33  #Chain   : 0
% 2.07/1.33  #Close   : 0
% 2.07/1.33  
% 2.07/1.33  Ordering : KBO
% 2.07/1.33  
% 2.07/1.33  Simplification rules
% 2.07/1.33  ----------------------
% 2.07/1.33  #Subsume      : 2
% 2.07/1.33  #Demod        : 40
% 2.07/1.33  #Tautology    : 50
% 2.07/1.33  #SimpNegUnit  : 0
% 2.07/1.33  #BackRed      : 16
% 2.07/1.33  
% 2.07/1.33  #Partial instantiations: 0
% 2.07/1.33  #Strategies tried      : 1
% 2.07/1.33  
% 2.07/1.33  Timing (in seconds)
% 2.07/1.33  ----------------------
% 2.07/1.33  Preprocessing        : 0.35
% 2.07/1.33  Parsing              : 0.19
% 2.07/1.33  CNF conversion       : 0.02
% 2.07/1.33  Main loop            : 0.18
% 2.07/1.33  Inferencing          : 0.06
% 2.07/1.33  Reduction            : 0.06
% 2.07/1.33  Demodulation         : 0.05
% 2.07/1.33  BG Simplification    : 0.01
% 2.07/1.33  Subsumption          : 0.02
% 2.07/1.33  Abstraction          : 0.01
% 2.07/1.33  MUC search           : 0.00
% 2.07/1.33  Cooper               : 0.00
% 2.07/1.33  Total                : 0.56
% 2.07/1.33  Index Insertion      : 0.00
% 2.07/1.33  Index Deletion       : 0.00
% 2.07/1.33  Index Matching       : 0.00
% 2.07/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
