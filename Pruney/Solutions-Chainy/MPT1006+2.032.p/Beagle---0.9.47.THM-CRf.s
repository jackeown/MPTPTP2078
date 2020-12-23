%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 105 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 198 expanded)
%              Number of equality atoms :   36 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_75,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relset_1(A_20,B_21,C_22) = k1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_96,plain,(
    ! [B_26] : k1_relset_1(k1_xboole_0,B_26,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_93])).

tff(c_32,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [B_11,C_12] :
      ( k1_relset_1(k1_xboole_0,B_11,C_12) = k1_xboole_0
      | ~ v1_funct_2(C_12,k1_xboole_0,B_11)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_115,plain,
    ( k1_relset_1(k1_xboole_0,'#skF_1','#skF_3') = k1_xboole_0
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_118,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_96,c_115])).

tff(c_119,plain,(
    ! [B_26] : k1_relset_1(k1_xboole_0,B_26,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_96])).

tff(c_16,plain,(
    ! [C_12,B_11] :
      ( v1_funct_2(C_12,k1_xboole_0,B_11)
      | k1_relset_1(k1_xboole_0,B_11,C_12) != k1_xboole_0
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [C_49,B_50] :
      ( v1_funct_2(C_49,k1_xboole_0,B_50)
      | k1_relset_1(k1_xboole_0,B_50,C_49) != k1_xboole_0
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_191,plain,(
    ! [B_50] :
      ( v1_funct_2('#skF_3',k1_xboole_0,B_50)
      | k1_relset_1(k1_xboole_0,B_50,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_35,c_189])).

tff(c_194,plain,(
    ! [B_50] : v1_funct_2('#skF_3',k1_xboole_0,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_191])).

tff(c_147,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k8_relset_1(A_35,B_36,C_37,D_38) = k10_relat_1(C_37,D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_165,plain,(
    ! [B_44,C_45,D_46] :
      ( k8_relset_1(k1_xboole_0,B_44,C_45,D_46) = k10_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_147])).

tff(c_168,plain,(
    ! [B_44,D_46] : k8_relset_1(k1_xboole_0,B_44,'#skF_3',D_46) = k10_relat_1('#skF_3',D_46) ),
    inference(resolution,[status(thm)],[c_35,c_165])).

tff(c_24,plain,(
    ! [B_14,C_15] :
      ( k8_relset_1(k1_xboole_0,B_14,C_15,B_14) = k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_2(C_15,k1_xboole_0,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_209,plain,(
    ! [B_52,C_53] :
      ( k8_relset_1(k1_xboole_0,B_52,C_53,B_52) = k1_xboole_0
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(C_53,k1_xboole_0,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_211,plain,(
    ! [B_52] :
      ( k8_relset_1(k1_xboole_0,B_52,'#skF_3',B_52) = k1_xboole_0
      | ~ v1_funct_2('#skF_3',k1_xboole_0,B_52)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_35,c_209])).

tff(c_214,plain,(
    ! [B_52] : k10_relat_1('#skF_3',B_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_194,c_168,c_211])).

tff(c_28,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_169,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_28])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.17/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.17/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.26  
% 2.17/1.27  tff(f_78, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.17/1.27  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.27  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.27  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.17/1.27  tff(f_39, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.17/1.27  tff(f_69, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 2.17/1.27  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.27  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.27  tff(c_35, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 2.17/1.27  tff(c_75, plain, (![A_20, B_21, C_22]: (k1_relset_1(A_20, B_21, C_22)=k1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.27  tff(c_93, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 2.17/1.27  tff(c_96, plain, (![B_26]: (k1_relset_1(k1_xboole_0, B_26, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_35, c_93])).
% 2.17/1.27  tff(c_32, plain, (v1_funct_2('#skF_3', k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.27  tff(c_20, plain, (![B_11, C_12]: (k1_relset_1(k1_xboole_0, B_11, C_12)=k1_xboole_0 | ~v1_funct_2(C_12, k1_xboole_0, B_11) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_11))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.27  tff(c_113, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20])).
% 2.17/1.27  tff(c_115, plain, (k1_relset_1(k1_xboole_0, '#skF_1', '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.17/1.27  tff(c_118, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_35, c_96, c_115])).
% 2.17/1.27  tff(c_119, plain, (![B_26]: (k1_relset_1(k1_xboole_0, B_26, '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_96])).
% 2.17/1.27  tff(c_16, plain, (![C_12, B_11]: (v1_funct_2(C_12, k1_xboole_0, B_11) | k1_relset_1(k1_xboole_0, B_11, C_12)!=k1_xboole_0 | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_11))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.27  tff(c_189, plain, (![C_49, B_50]: (v1_funct_2(C_49, k1_xboole_0, B_50) | k1_relset_1(k1_xboole_0, B_50, C_49)!=k1_xboole_0 | ~m1_subset_1(C_49, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.17/1.27  tff(c_191, plain, (![B_50]: (v1_funct_2('#skF_3', k1_xboole_0, B_50) | k1_relset_1(k1_xboole_0, B_50, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_189])).
% 2.17/1.27  tff(c_194, plain, (![B_50]: (v1_funct_2('#skF_3', k1_xboole_0, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_191])).
% 2.17/1.27  tff(c_147, plain, (![A_35, B_36, C_37, D_38]: (k8_relset_1(A_35, B_36, C_37, D_38)=k10_relat_1(C_37, D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.27  tff(c_165, plain, (![B_44, C_45, D_46]: (k8_relset_1(k1_xboole_0, B_44, C_45, D_46)=k10_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_147])).
% 2.17/1.27  tff(c_168, plain, (![B_44, D_46]: (k8_relset_1(k1_xboole_0, B_44, '#skF_3', D_46)=k10_relat_1('#skF_3', D_46))), inference(resolution, [status(thm)], [c_35, c_165])).
% 2.17/1.27  tff(c_24, plain, (![B_14, C_15]: (k8_relset_1(k1_xboole_0, B_14, C_15, B_14)=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_2(C_15, k1_xboole_0, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.27  tff(c_209, plain, (![B_52, C_53]: (k8_relset_1(k1_xboole_0, B_52, C_53, B_52)=k1_xboole_0 | ~m1_subset_1(C_53, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(C_53, k1_xboole_0, B_52) | ~v1_funct_1(C_53))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24])).
% 2.17/1.27  tff(c_211, plain, (![B_52]: (k8_relset_1(k1_xboole_0, B_52, '#skF_3', B_52)=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, B_52) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_35, c_209])).
% 2.17/1.27  tff(c_214, plain, (![B_52]: (k10_relat_1('#skF_3', B_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_194, c_168, c_211])).
% 2.17/1.27  tff(c_28, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.27  tff(c_169, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_168, c_28])).
% 2.17/1.27  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_169])).
% 2.17/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  Inference rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Ref     : 0
% 2.17/1.27  #Sup     : 41
% 2.17/1.27  #Fact    : 0
% 2.17/1.27  #Define  : 0
% 2.17/1.27  #Split   : 1
% 2.17/1.27  #Chain   : 0
% 2.17/1.27  #Close   : 0
% 2.17/1.27  
% 2.17/1.27  Ordering : KBO
% 2.17/1.27  
% 2.17/1.27  Simplification rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Subsume      : 0
% 2.17/1.27  #Demod        : 22
% 2.17/1.27  #Tautology    : 31
% 2.17/1.27  #SimpNegUnit  : 0
% 2.17/1.27  #BackRed      : 6
% 2.17/1.27  
% 2.17/1.27  #Partial instantiations: 0
% 2.17/1.27  #Strategies tried      : 1
% 2.17/1.27  
% 2.17/1.27  Timing (in seconds)
% 2.17/1.27  ----------------------
% 2.17/1.27  Preprocessing        : 0.32
% 2.17/1.27  Parsing              : 0.17
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.17
% 2.17/1.27  Inferencing          : 0.06
% 2.17/1.27  Reduction            : 0.06
% 2.17/1.27  Demodulation         : 0.04
% 2.17/1.27  BG Simplification    : 0.02
% 2.17/1.27  Subsumption          : 0.03
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.53
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
