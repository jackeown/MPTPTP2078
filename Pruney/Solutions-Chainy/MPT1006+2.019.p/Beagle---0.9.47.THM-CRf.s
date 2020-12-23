%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:05 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 207 expanded)
%              Number of leaves         :   24 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 358 expanded)
%              Number of equality atoms :   18 ( 128 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_89,plain,(
    ! [C_32] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_94,plain,(
    ! [C_35] :
      ( v1_xboole_0(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_104,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_29,c_94])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_124,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_12])).

tff(c_105,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( k8_relset_1(A_36,B_37,C_38,D_39) = k10_relat_1(C_38,D_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [A_36,B_37,D_39] : k8_relset_1(A_36,B_37,k1_xboole_0,D_39) = k10_relat_1(k1_xboole_0,D_39) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_223,plain,(
    ! [A_52,B_53,D_54] : k8_relset_1(A_52,B_53,'#skF_3',D_54) = k10_relat_1('#skF_3',D_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_113])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( m1_subset_1(k8_relset_1(A_12,B_13,C_14,D_15),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_229,plain,(
    ! [D_54,A_52,B_53] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_18])).

tff(c_237,plain,(
    ! [D_55,A_56] : m1_subset_1(k10_relat_1('#skF_3',D_55),k1_zfmisc_1(A_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_229])).

tff(c_93,plain,(
    ! [C_32] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_118,plain,(
    ! [C_32] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_93])).

tff(c_256,plain,(
    ! [D_57] : v1_xboole_0(k10_relat_1('#skF_3',D_57)) ),
    inference(resolution,[status(thm)],[c_237,c_118])).

tff(c_123,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_4])).

tff(c_260,plain,(
    ! [D_57] : k10_relat_1('#skF_3',D_57) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_256,c_123])).

tff(c_221,plain,(
    ! [A_36,B_37,D_39] : k8_relset_1(A_36,B_37,'#skF_3',D_39) = k10_relat_1('#skF_3',D_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_113])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_22])).

tff(c_222,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_122])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.23  
% 2.14/1.24  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.14/1.24  tff(f_68, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.14/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.14/1.24  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.14/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.14/1.24  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.14/1.24  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.14/1.24  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.14/1.24  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.24  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.24  tff(c_29, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 2.14/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.14/1.24  tff(c_79, plain, (![C_32, A_33, B_34]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.24  tff(c_89, plain, (![C_32]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_79])).
% 2.14/1.24  tff(c_94, plain, (![C_35]: (v1_xboole_0(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_89])).
% 2.14/1.24  tff(c_104, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_29, c_94])).
% 2.14/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.14/1.24  tff(c_117, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_104, c_4])).
% 2.14/1.24  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.24  tff(c_124, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_12])).
% 2.14/1.24  tff(c_105, plain, (![A_36, B_37, C_38, D_39]: (k8_relset_1(A_36, B_37, C_38, D_39)=k10_relat_1(C_38, D_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.14/1.24  tff(c_113, plain, (![A_36, B_37, D_39]: (k8_relset_1(A_36, B_37, k1_xboole_0, D_39)=k10_relat_1(k1_xboole_0, D_39))), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.14/1.24  tff(c_223, plain, (![A_52, B_53, D_54]: (k8_relset_1(A_52, B_53, '#skF_3', D_54)=k10_relat_1('#skF_3', D_54))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_113])).
% 2.14/1.24  tff(c_18, plain, (![A_12, B_13, C_14, D_15]: (m1_subset_1(k8_relset_1(A_12, B_13, C_14, D_15), k1_zfmisc_1(A_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.24  tff(c_229, plain, (![D_54, A_52, B_53]: (m1_subset_1(k10_relat_1('#skF_3', D_54), k1_zfmisc_1(A_52)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(superposition, [status(thm), theory('equality')], [c_223, c_18])).
% 2.14/1.24  tff(c_237, plain, (![D_55, A_56]: (m1_subset_1(k10_relat_1('#skF_3', D_55), k1_zfmisc_1(A_56)))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_229])).
% 2.14/1.24  tff(c_93, plain, (![C_32]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_89])).
% 2.14/1.24  tff(c_118, plain, (![C_32]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_93])).
% 2.14/1.24  tff(c_256, plain, (![D_57]: (v1_xboole_0(k10_relat_1('#skF_3', D_57)))), inference(resolution, [status(thm)], [c_237, c_118])).
% 2.14/1.24  tff(c_123, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_4])).
% 2.14/1.24  tff(c_260, plain, (![D_57]: (k10_relat_1('#skF_3', D_57)='#skF_3')), inference(resolution, [status(thm)], [c_256, c_123])).
% 2.14/1.24  tff(c_221, plain, (![A_36, B_37, D_39]: (k8_relset_1(A_36, B_37, '#skF_3', D_39)=k10_relat_1('#skF_3', D_39))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_113])).
% 2.14/1.24  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.24  tff(c_122, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_22])).
% 2.14/1.24  tff(c_222, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_122])).
% 2.14/1.24  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_222])).
% 2.14/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  Inference rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Ref     : 0
% 2.14/1.24  #Sup     : 50
% 2.14/1.24  #Fact    : 0
% 2.14/1.24  #Define  : 0
% 2.14/1.24  #Split   : 0
% 2.14/1.24  #Chain   : 0
% 2.14/1.24  #Close   : 0
% 2.14/1.24  
% 2.14/1.24  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 5
% 2.14/1.24  #Demod        : 38
% 2.14/1.24  #Tautology    : 28
% 2.14/1.24  #SimpNegUnit  : 0
% 2.14/1.24  #BackRed      : 17
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.25  Preprocessing        : 0.30
% 2.14/1.25  Parsing              : 0.16
% 2.14/1.25  CNF conversion       : 0.02
% 2.14/1.25  Main loop            : 0.18
% 2.14/1.25  Inferencing          : 0.06
% 2.14/1.25  Reduction            : 0.06
% 2.14/1.25  Demodulation         : 0.04
% 2.14/1.25  BG Simplification    : 0.01
% 2.14/1.25  Subsumption          : 0.03
% 2.14/1.25  Abstraction          : 0.01
% 2.14/1.25  MUC search           : 0.00
% 2.14/1.25  Cooper               : 0.00
% 2.14/1.25  Total                : 0.51
% 2.14/1.25  Index Insertion      : 0.00
% 2.14/1.25  Index Deletion       : 0.00
% 2.14/1.25  Index Matching       : 0.00
% 2.14/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
