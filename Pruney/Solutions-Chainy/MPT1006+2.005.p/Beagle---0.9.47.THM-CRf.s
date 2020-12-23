%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 182 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 ( 267 expanded)
%              Number of equality atoms :   17 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
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
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_37])).

tff(c_87,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_87])).

tff(c_98,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_112,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_98,c_43])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_131,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_50])).

tff(c_312,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( m1_subset_1(k8_relset_1(A_60,B_61,C_62,D_63),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_548,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( v1_xboole_0(k8_relset_1(A_97,B_98,C_99,D_100))
      | ~ v1_xboole_0(A_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(resolution,[status(thm)],[c_312,c_14])).

tff(c_567,plain,(
    ! [A_101,B_102,D_103] :
      ( v1_xboole_0(k8_relset_1(A_101,B_102,'#skF_4',D_103))
      | ~ v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_131,c_548])).

tff(c_126,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_43])).

tff(c_572,plain,(
    ! [A_104,B_105,D_106] :
      ( k8_relset_1(A_104,B_105,'#skF_4',D_106) = '#skF_4'
      | ~ v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_567,c_126])).

tff(c_581,plain,(
    ! [B_105,D_106] : k8_relset_1('#skF_4',B_105,'#skF_4',D_106) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_98,c_572])).

tff(c_30,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_30])).

tff(c_128,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_76])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.33  
% 2.13/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.13/1.33  
% 2.13/1.33  %Foreground sorts:
% 2.13/1.33  
% 2.13/1.33  
% 2.13/1.33  %Background operators:
% 2.13/1.33  
% 2.13/1.33  
% 2.13/1.33  %Foreground operators:
% 2.13/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.13/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.33  
% 2.54/1.34  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.54/1.34  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.54/1.34  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.54/1.34  tff(f_85, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.54/1.34  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.54/1.34  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.54/1.34  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.54/1.34  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.34  tff(c_38, plain, (![A_25]: (k1_xboole_0=A_25 | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.34  tff(c_42, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_38])).
% 2.54/1.34  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.34  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.54/1.34  tff(c_37, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.54/1.34  tff(c_49, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_37])).
% 2.54/1.34  tff(c_87, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.54/1.34  tff(c_93, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_49, c_87])).
% 2.54/1.34  tff(c_98, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_93])).
% 2.54/1.34  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.34  tff(c_43, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.54/1.34  tff(c_112, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_98, c_43])).
% 2.54/1.34  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.34  tff(c_50, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 2.54/1.34  tff(c_131, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_50])).
% 2.54/1.34  tff(c_312, plain, (![A_60, B_61, C_62, D_63]: (m1_subset_1(k8_relset_1(A_60, B_61, C_62, D_63), k1_zfmisc_1(A_60)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.34  tff(c_14, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.54/1.34  tff(c_548, plain, (![A_97, B_98, C_99, D_100]: (v1_xboole_0(k8_relset_1(A_97, B_98, C_99, D_100)) | ~v1_xboole_0(A_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(resolution, [status(thm)], [c_312, c_14])).
% 2.54/1.34  tff(c_567, plain, (![A_101, B_102, D_103]: (v1_xboole_0(k8_relset_1(A_101, B_102, '#skF_4', D_103)) | ~v1_xboole_0(A_101))), inference(resolution, [status(thm)], [c_131, c_548])).
% 2.54/1.34  tff(c_126, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_43])).
% 2.54/1.34  tff(c_572, plain, (![A_104, B_105, D_106]: (k8_relset_1(A_104, B_105, '#skF_4', D_106)='#skF_4' | ~v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_567, c_126])).
% 2.54/1.34  tff(c_581, plain, (![B_105, D_106]: (k8_relset_1('#skF_4', B_105, '#skF_4', D_106)='#skF_4')), inference(resolution, [status(thm)], [c_98, c_572])).
% 2.54/1.34  tff(c_30, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.54/1.34  tff(c_76, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_30])).
% 2.54/1.34  tff(c_128, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_76])).
% 2.54/1.34  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_581, c_128])).
% 2.54/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  Inference rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Ref     : 0
% 2.54/1.34  #Sup     : 112
% 2.54/1.34  #Fact    : 0
% 2.54/1.34  #Define  : 0
% 2.54/1.34  #Split   : 1
% 2.54/1.34  #Chain   : 0
% 2.54/1.34  #Close   : 0
% 2.54/1.34  
% 2.54/1.34  Ordering : KBO
% 2.54/1.34  
% 2.54/1.34  Simplification rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Subsume      : 6
% 2.54/1.34  #Demod        : 106
% 2.54/1.34  #Tautology    : 56
% 2.54/1.34  #SimpNegUnit  : 2
% 2.54/1.34  #BackRed      : 21
% 2.54/1.34  
% 2.54/1.34  #Partial instantiations: 0
% 2.54/1.34  #Strategies tried      : 1
% 2.54/1.34  
% 2.54/1.34  Timing (in seconds)
% 2.54/1.34  ----------------------
% 2.54/1.35  Preprocessing        : 0.30
% 2.54/1.35  Parsing              : 0.16
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.27
% 2.54/1.35  Inferencing          : 0.10
% 2.54/1.35  Reduction            : 0.09
% 2.54/1.35  Demodulation         : 0.06
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.05
% 2.54/1.35  Abstraction          : 0.02
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.61
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
