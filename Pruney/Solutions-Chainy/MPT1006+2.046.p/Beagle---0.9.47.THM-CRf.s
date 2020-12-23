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
% DateTime   : Thu Dec  3 10:14:08 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 157 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 ( 216 expanded)
%              Number of equality atoms :   23 ( 137 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_42,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
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
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_12,plain,(
    ! [A_7] : k9_relat_1(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_27,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_73,plain,(
    ! [A_20,B_21] :
      ( k9_relat_1(k6_relat_1(A_20),B_21) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_27,c_73])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_79])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_8])).

tff(c_87,plain,(
    ! [A_7] : k9_relat_1('#skF_3',A_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_12])).

tff(c_91,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_14])).

tff(c_88,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_6])).

tff(c_160,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(k8_relset_1(A_32,B_33,C_34,D_35),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k9_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k9_relat_1(k6_relat_1(A_43),k8_relset_1(A_43,B_44,C_45,D_46)) = k8_relset_1(A_43,B_44,C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(resolution,[status(thm)],[c_160,c_16])).

tff(c_190,plain,(
    ! [B_2,C_45,D_46] :
      ( k9_relat_1(k6_relat_1('#skF_3'),k8_relset_1('#skF_3',B_2,C_45,D_46)) = k8_relset_1('#skF_3',B_2,C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_180])).

tff(c_215,plain,(
    ! [B_53,C_54,D_55] :
      ( k8_relset_1('#skF_3',B_53,C_54,D_55) = '#skF_3'
      | ~ m1_subset_1(C_54,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_91,c_190])).

tff(c_224,plain,(
    ! [B_53,D_55] : k8_relset_1('#skF_3',B_53,'#skF_3',D_55) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_85,c_215])).

tff(c_20,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_20])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_84])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.20  
% 1.84/1.20  %Foreground sorts:
% 1.84/1.20  
% 1.84/1.20  
% 1.84/1.20  %Background operators:
% 1.84/1.20  
% 1.84/1.20  
% 1.84/1.20  %Foreground operators:
% 1.84/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.20  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.84/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.84/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.84/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.20  
% 1.84/1.21  tff(f_41, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.84/1.21  tff(f_42, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.84/1.21  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.21  tff(f_59, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.84/1.21  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.84/1.21  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.84/1.21  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.84/1.21  tff(c_12, plain, (![A_7]: (k9_relat_1(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.21  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.21  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.21  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.84/1.21  tff(c_27, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22])).
% 1.84/1.21  tff(c_73, plain, (![A_20, B_21]: (k9_relat_1(k6_relat_1(A_20), B_21)=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.21  tff(c_79, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_27, c_73])).
% 1.84/1.21  tff(c_82, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_79])).
% 1.84/1.21  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.21  tff(c_85, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_8])).
% 1.84/1.21  tff(c_87, plain, (![A_7]: (k9_relat_1('#skF_3', A_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_12])).
% 1.84/1.21  tff(c_91, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_14])).
% 1.84/1.21  tff(c_88, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_6])).
% 1.84/1.21  tff(c_160, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(k8_relset_1(A_32, B_33, C_34, D_35), k1_zfmisc_1(A_32)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.21  tff(c_16, plain, (![A_8, B_9]: (k9_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.21  tff(c_180, plain, (![A_43, B_44, C_45, D_46]: (k9_relat_1(k6_relat_1(A_43), k8_relset_1(A_43, B_44, C_45, D_46))=k8_relset_1(A_43, B_44, C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(resolution, [status(thm)], [c_160, c_16])).
% 1.84/1.21  tff(c_190, plain, (![B_2, C_45, D_46]: (k9_relat_1(k6_relat_1('#skF_3'), k8_relset_1('#skF_3', B_2, C_45, D_46))=k8_relset_1('#skF_3', B_2, C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_180])).
% 1.84/1.21  tff(c_215, plain, (![B_53, C_54, D_55]: (k8_relset_1('#skF_3', B_53, C_54, D_55)='#skF_3' | ~m1_subset_1(C_54, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_91, c_190])).
% 1.84/1.21  tff(c_224, plain, (![B_53, D_55]: (k8_relset_1('#skF_3', B_53, '#skF_3', D_55)='#skF_3')), inference(resolution, [status(thm)], [c_85, c_215])).
% 1.84/1.21  tff(c_20, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.84/1.21  tff(c_84, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_20])).
% 1.84/1.21  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_84])).
% 1.84/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  Inference rules
% 1.84/1.21  ----------------------
% 1.84/1.21  #Ref     : 0
% 1.84/1.21  #Sup     : 48
% 1.84/1.21  #Fact    : 0
% 1.84/1.21  #Define  : 0
% 1.84/1.21  #Split   : 0
% 1.84/1.21  #Chain   : 0
% 1.84/1.21  #Close   : 0
% 1.84/1.21  
% 1.84/1.21  Ordering : KBO
% 1.84/1.21  
% 1.84/1.21  Simplification rules
% 1.84/1.21  ----------------------
% 1.84/1.21  #Subsume      : 1
% 1.84/1.21  #Demod        : 42
% 1.84/1.21  #Tautology    : 34
% 1.84/1.21  #SimpNegUnit  : 0
% 1.84/1.21  #BackRed      : 10
% 1.84/1.21  
% 1.84/1.21  #Partial instantiations: 0
% 1.84/1.21  #Strategies tried      : 1
% 1.84/1.21  
% 1.84/1.21  Timing (in seconds)
% 1.84/1.21  ----------------------
% 1.84/1.22  Preprocessing        : 0.28
% 1.84/1.22  Parsing              : 0.16
% 1.84/1.22  CNF conversion       : 0.02
% 1.84/1.22  Main loop            : 0.18
% 1.84/1.22  Inferencing          : 0.07
% 1.84/1.22  Reduction            : 0.06
% 1.84/1.22  Demodulation         : 0.04
% 1.84/1.22  BG Simplification    : 0.01
% 1.84/1.22  Subsumption          : 0.03
% 1.84/1.22  Abstraction          : 0.01
% 1.84/1.22  MUC search           : 0.00
% 1.84/1.22  Cooper               : 0.00
% 1.84/1.22  Total                : 0.48
% 1.84/1.22  Index Insertion      : 0.00
% 1.84/1.22  Index Deletion       : 0.00
% 1.84/1.22  Index Matching       : 0.00
% 1.84/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
