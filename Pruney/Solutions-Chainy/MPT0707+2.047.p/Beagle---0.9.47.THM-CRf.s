%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:22 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  71 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_64,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_18,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [B_14,A_13] : k5_relat_1(k6_relat_1(B_14),k6_relat_1(A_13)) = k6_relat_1(k3_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    ! [A_30,B_31] :
      ( k10_relat_1(A_30,k1_relat_1(B_31)) = k1_relat_1(k5_relat_1(A_30,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [A_30,A_8] :
      ( k1_relat_1(k5_relat_1(A_30,k6_relat_1(A_8))) = k10_relat_1(A_30,A_8)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_128,plain,(
    ! [A_36,A_37] :
      ( k1_relat_1(k5_relat_1(A_36,k6_relat_1(A_37))) = k10_relat_1(A_36,A_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_99])).

tff(c_140,plain,(
    ! [A_13,B_14] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_13,B_14))) = k10_relat_1(k6_relat_1(B_14),A_13)
      | ~ v1_relat_1(k6_relat_1(B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_144,plain,(
    ! [B_14,A_13] : k10_relat_1(k6_relat_1(B_14),A_13) = k3_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_140])).

tff(c_16,plain,(
    ! [A_9] : v1_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_15] : k2_funct_1(k6_relat_1(A_15)) = k6_relat_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,(
    ! [B_32,A_33] :
      ( k9_relat_1(k2_funct_1(B_32),A_33) = k10_relat_1(B_32,A_33)
      | ~ v2_funct_1(B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    ! [A_15,A_33] :
      ( k9_relat_1(k6_relat_1(A_15),A_33) = k10_relat_1(k6_relat_1(A_15),A_33)
      | ~ v2_funct_1(k6_relat_1(A_15))
      | ~ v1_funct_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_104])).

tff(c_117,plain,(
    ! [A_15,A_33] : k9_relat_1(k6_relat_1(A_15),A_33) = k10_relat_1(k6_relat_1(A_15),A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_20,c_113])).

tff(c_28,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_118,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_28])).

tff(c_162,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_118])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.96/1.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.96/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.20  
% 1.96/1.21  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.96/1.21  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.96/1.21  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.96/1.21  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.96/1.21  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.96/1.21  tff(f_62, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.96/1.21  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 1.96/1.21  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.96/1.21  tff(f_64, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 1.96/1.21  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 1.96/1.21  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.21  tff(c_64, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.21  tff(c_72, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_64])).
% 1.96/1.21  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.21  tff(c_76, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_72, c_2])).
% 1.96/1.21  tff(c_18, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.21  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.96/1.21  tff(c_24, plain, (![B_14, A_13]: (k5_relat_1(k6_relat_1(B_14), k6_relat_1(A_13))=k6_relat_1(k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.21  tff(c_90, plain, (![A_30, B_31]: (k10_relat_1(A_30, k1_relat_1(B_31))=k1_relat_1(k5_relat_1(A_30, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.96/1.21  tff(c_99, plain, (![A_30, A_8]: (k1_relat_1(k5_relat_1(A_30, k6_relat_1(A_8)))=k10_relat_1(A_30, A_8) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 1.96/1.21  tff(c_128, plain, (![A_36, A_37]: (k1_relat_1(k5_relat_1(A_36, k6_relat_1(A_37)))=k10_relat_1(A_36, A_37) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_99])).
% 1.96/1.21  tff(c_140, plain, (![A_13, B_14]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_13, B_14)))=k10_relat_1(k6_relat_1(B_14), A_13) | ~v1_relat_1(k6_relat_1(B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_128])).
% 1.96/1.21  tff(c_144, plain, (![B_14, A_13]: (k10_relat_1(k6_relat_1(B_14), A_13)=k3_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_140])).
% 1.96/1.21  tff(c_16, plain, (![A_9]: (v1_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.21  tff(c_20, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.21  tff(c_26, plain, (![A_15]: (k2_funct_1(k6_relat_1(A_15))=k6_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.21  tff(c_104, plain, (![B_32, A_33]: (k9_relat_1(k2_funct_1(B_32), A_33)=k10_relat_1(B_32, A_33) | ~v2_funct_1(B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.21  tff(c_113, plain, (![A_15, A_33]: (k9_relat_1(k6_relat_1(A_15), A_33)=k10_relat_1(k6_relat_1(A_15), A_33) | ~v2_funct_1(k6_relat_1(A_15)) | ~v1_funct_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_104])).
% 1.96/1.21  tff(c_117, plain, (![A_15, A_33]: (k9_relat_1(k6_relat_1(A_15), A_33)=k10_relat_1(k6_relat_1(A_15), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_20, c_113])).
% 1.96/1.21  tff(c_28, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.21  tff(c_118, plain, (k10_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_28])).
% 1.96/1.21  tff(c_162, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_118])).
% 1.96/1.21  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_162])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 29
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 0
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 0
% 1.96/1.21  #Demod        : 14
% 1.96/1.21  #Tautology    : 22
% 1.96/1.21  #SimpNegUnit  : 0
% 1.96/1.21  #BackRed      : 3
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.22  Preprocessing        : 0.30
% 1.96/1.22  Parsing              : 0.16
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.14
% 1.96/1.22  Inferencing          : 0.06
% 1.96/1.22  Reduction            : 0.05
% 1.96/1.22  Demodulation         : 0.04
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.02
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.47
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
