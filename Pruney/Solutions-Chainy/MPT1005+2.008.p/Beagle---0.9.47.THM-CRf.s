%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:00 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 258 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 ( 388 expanded)
%              Number of equality atoms :   25 ( 150 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_46,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_25])).

tff(c_103,plain,(
    ! [B_21,A_22] :
      ( v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_103])).

tff(c_109,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_113,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_109,c_45])).

tff(c_14,plain,(
    ! [A_7] : k9_relat_1(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [A_7] : k9_relat_1('#skF_1',A_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_14])).

tff(c_115,plain,(
    ! [A_7] : k9_relat_1('#skF_4',A_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_46])).

tff(c_117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_49])).

tff(c_54,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_10])).

tff(c_121,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_54])).

tff(c_168,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k7_relset_1(A_27,B_28,C_29,D_30) = k9_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_190,plain,(
    ! [B_33,C_34,D_35] :
      ( k7_relset_1('#skF_4',B_33,C_34,D_35) = k9_relat_1(C_34,D_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_168])).

tff(c_192,plain,(
    ! [B_33,D_35] : k7_relset_1('#skF_4',B_33,'#skF_4',D_35) = k9_relat_1('#skF_4',D_35) ),
    inference(resolution,[status(thm)],[c_117,c_190])).

tff(c_194,plain,(
    ! [B_33,D_35] : k7_relset_1('#skF_4',B_33,'#skF_4',D_35) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_192])).

tff(c_18,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_18])).

tff(c_120,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_62])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:07:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.83/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.17  
% 1.83/1.18  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.83/1.18  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.83/1.18  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.83/1.18  tff(f_59, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 1.83/1.18  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 1.83/1.18  tff(f_46, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.83/1.18  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.83/1.18  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.18  tff(c_40, plain, (![A_14]: (k1_xboole_0=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_44, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.83/1.18  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.18  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.83/1.18  tff(c_25, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.83/1.18  tff(c_49, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_25])).
% 1.83/1.18  tff(c_103, plain, (![B_21, A_22]: (v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.18  tff(c_106, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_49, c_103])).
% 1.83/1.18  tff(c_109, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_106])).
% 1.83/1.18  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_45, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2])).
% 1.83/1.18  tff(c_113, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_109, c_45])).
% 1.83/1.18  tff(c_14, plain, (![A_7]: (k9_relat_1(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.83/1.18  tff(c_46, plain, (![A_7]: (k9_relat_1('#skF_1', A_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_14])).
% 1.83/1.18  tff(c_115, plain, (![A_7]: (k9_relat_1('#skF_4', A_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_46])).
% 1.83/1.18  tff(c_117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_49])).
% 1.83/1.18  tff(c_54, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_10])).
% 1.83/1.18  tff(c_121, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_54])).
% 1.83/1.18  tff(c_168, plain, (![A_27, B_28, C_29, D_30]: (k7_relset_1(A_27, B_28, C_29, D_30)=k9_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.18  tff(c_190, plain, (![B_33, C_34, D_35]: (k7_relset_1('#skF_4', B_33, C_34, D_35)=k9_relat_1(C_34, D_35) | ~m1_subset_1(C_34, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_121, c_168])).
% 1.83/1.18  tff(c_192, plain, (![B_33, D_35]: (k7_relset_1('#skF_4', B_33, '#skF_4', D_35)=k9_relat_1('#skF_4', D_35))), inference(resolution, [status(thm)], [c_117, c_190])).
% 1.83/1.18  tff(c_194, plain, (![B_33, D_35]: (k7_relset_1('#skF_4', B_33, '#skF_4', D_35)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_192])).
% 1.83/1.18  tff(c_18, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.83/1.18  tff(c_62, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_18])).
% 1.83/1.18  tff(c_120, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_62])).
% 1.83/1.18  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_120])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 39
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 0
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 0
% 1.83/1.18  #Demod        : 37
% 1.83/1.18  #Tautology    : 34
% 1.83/1.18  #SimpNegUnit  : 0
% 1.83/1.18  #BackRed      : 16
% 1.83/1.18  
% 1.83/1.18  #Partial instantiations: 0
% 1.83/1.18  #Strategies tried      : 1
% 1.83/1.18  
% 1.83/1.18  Timing (in seconds)
% 1.83/1.18  ----------------------
% 1.83/1.19  Preprocessing        : 0.29
% 1.83/1.19  Parsing              : 0.15
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.13
% 1.83/1.19  Inferencing          : 0.05
% 1.83/1.19  Reduction            : 0.05
% 1.83/1.19  Demodulation         : 0.04
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.44
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
