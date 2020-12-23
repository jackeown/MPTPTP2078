%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:00 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
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
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_55,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_72,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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
    ! [A_41] : k9_relat_1(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    ! [A_41] : k9_relat_1('#skF_4',A_41) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_36])).

tff(c_30,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_181,plain,(
    ! [A_34] : m1_subset_1('#skF_4',k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_30])).

tff(c_294,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_301,plain,(
    ! [A_89,B_90,D_92] : k7_relset_1(A_89,B_90,'#skF_4',D_92) = k9_relat_1('#skF_4',D_92) ),
    inference(resolution,[status(thm)],[c_181,c_294])).

tff(c_305,plain,(
    ! [A_89,B_90,D_92] : k7_relset_1(A_89,B_90,'#skF_4',D_92) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_301])).

tff(c_40,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_174,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_40])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.34  
% 2.08/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.08/1.34  
% 2.08/1.34  %Foreground sorts:
% 2.08/1.34  
% 2.08/1.34  
% 2.08/1.34  %Background operators:
% 2.08/1.34  
% 2.08/1.34  
% 2.08/1.34  %Foreground operators:
% 2.08/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.08/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.08/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.08/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.34  
% 2.08/1.36  tff(f_50, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.08/1.36  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.08/1.36  tff(f_85, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 2.08/1.36  tff(f_55, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.08/1.36  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.08/1.36  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.08/1.36  tff(f_72, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.08/1.36  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.08/1.36  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.08/1.36  tff(c_24, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.36  tff(c_22, plain, (![B_31]: (k2_zfmisc_1(k1_xboole_0, B_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.36  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.08/1.36  tff(c_47, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42])).
% 2.08/1.36  tff(c_48, plain, (m1_subset_1('#skF_4', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_47])).
% 2.08/1.36  tff(c_26, plain, (![A_32]: (v1_xboole_0('#skF_1'(A_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.36  tff(c_51, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.36  tff(c_55, plain, (![A_32]: ('#skF_1'(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_51])).
% 2.08/1.36  tff(c_63, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_26])).
% 2.08/1.36  tff(c_134, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.36  tff(c_137, plain, (![B_58]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_tarski(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_134])).
% 2.08/1.36  tff(c_154, plain, (![B_63]: (v1_xboole_0(B_63) | ~m1_subset_1(B_63, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_137])).
% 2.08/1.36  tff(c_163, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_154])).
% 2.08/1.36  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.36  tff(c_167, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_163, c_2])).
% 2.08/1.36  tff(c_36, plain, (![A_41]: (k9_relat_1(k1_xboole_0, A_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.36  tff(c_178, plain, (![A_41]: (k9_relat_1('#skF_4', A_41)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_36])).
% 2.08/1.36  tff(c_30, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.36  tff(c_181, plain, (![A_34]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_30])).
% 2.08/1.36  tff(c_294, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.36  tff(c_301, plain, (![A_89, B_90, D_92]: (k7_relset_1(A_89, B_90, '#skF_4', D_92)=k9_relat_1('#skF_4', D_92))), inference(resolution, [status(thm)], [c_181, c_294])).
% 2.08/1.36  tff(c_305, plain, (![A_89, B_90, D_92]: (k7_relset_1(A_89, B_90, '#skF_4', D_92)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_301])).
% 2.08/1.36  tff(c_40, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.08/1.36  tff(c_174, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_40])).
% 2.08/1.36  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_174])).
% 2.08/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.36  
% 2.08/1.36  Inference rules
% 2.08/1.36  ----------------------
% 2.08/1.36  #Ref     : 0
% 2.08/1.36  #Sup     : 59
% 2.08/1.36  #Fact    : 0
% 2.08/1.36  #Define  : 0
% 2.08/1.36  #Split   : 0
% 2.08/1.36  #Chain   : 0
% 2.08/1.36  #Close   : 0
% 2.08/1.36  
% 2.08/1.36  Ordering : KBO
% 2.08/1.36  
% 2.08/1.36  Simplification rules
% 2.08/1.36  ----------------------
% 2.08/1.36  #Subsume      : 2
% 2.08/1.36  #Demod        : 40
% 2.08/1.36  #Tautology    : 50
% 2.08/1.36  #SimpNegUnit  : 0
% 2.08/1.36  #BackRed      : 16
% 2.08/1.36  
% 2.08/1.36  #Partial instantiations: 0
% 2.08/1.36  #Strategies tried      : 1
% 2.08/1.36  
% 2.08/1.36  Timing (in seconds)
% 2.08/1.36  ----------------------
% 2.08/1.36  Preprocessing        : 0.33
% 2.08/1.36  Parsing              : 0.17
% 2.08/1.36  CNF conversion       : 0.02
% 2.08/1.36  Main loop            : 0.17
% 2.08/1.36  Inferencing          : 0.06
% 2.08/1.36  Reduction            : 0.06
% 2.08/1.36  Demodulation         : 0.05
% 2.08/1.36  BG Simplification    : 0.01
% 2.08/1.36  Subsumption          : 0.02
% 2.08/1.36  Abstraction          : 0.01
% 2.08/1.36  MUC search           : 0.00
% 2.08/1.36  Cooper               : 0.00
% 2.08/1.36  Total                : 0.52
% 2.08/1.36  Index Insertion      : 0.00
% 2.08/1.36  Index Deletion       : 0.00
% 2.08/1.36  Index Matching       : 0.00
% 2.08/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
