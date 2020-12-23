%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:18 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   51 (  79 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 107 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [B_15,A_14] : k5_relat_1(k6_relat_1(B_15),k6_relat_1(A_14)) = k6_relat_1(k3_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    ! [B_36,A_37] :
      ( k9_relat_1(B_36,k2_relat_1(A_37)) = k2_relat_1(k5_relat_1(A_37,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_160,plain,(
    ! [A_10,B_36] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_10),B_36)) = k9_relat_1(B_36,A_10)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_140])).

tff(c_170,plain,(
    ! [A_38,B_39] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_38),B_39)) = k9_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_182,plain,(
    ! [A_14,B_15] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_14,B_15))) = k9_relat_1(k6_relat_1(A_14),B_15)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_170])).

tff(c_186,plain,(
    ! [A_14,B_15] : k9_relat_1(k6_relat_1(A_14),B_15) = k3_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_182])).

tff(c_24,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_10,A_31] :
      ( k7_relat_1(k6_relat_1(A_10),A_31) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_31)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_114,plain,(
    ! [A_32,A_33] :
      ( k7_relat_1(k6_relat_1(A_32),A_33) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_111])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_32,A_33] :
      ( k9_relat_1(k6_relat_1(A_32),A_33) = k2_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ r1_tarski(A_32,A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_126,plain,(
    ! [A_32,A_33] :
      ( k9_relat_1(k6_relat_1(A_32),A_33) = A_32
      | ~ r1_tarski(A_32,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_120])).

tff(c_227,plain,(
    ! [A_45,A_46] :
      ( k3_xboole_0(A_45,A_46) = A_45
      | ~ r1_tarski(A_45,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_126])).

tff(c_231,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_227])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_235,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_2])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.92/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.92/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.22  
% 2.00/1.23  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.00/1.23  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.00/1.23  tff(f_58, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.00/1.23  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.00/1.23  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.00/1.23  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.00/1.23  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.00/1.23  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.00/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.00/1.23  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.23  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.23  tff(c_22, plain, (![B_15, A_14]: (k5_relat_1(k6_relat_1(B_15), k6_relat_1(A_14))=k6_relat_1(k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.23  tff(c_140, plain, (![B_36, A_37]: (k9_relat_1(B_36, k2_relat_1(A_37))=k2_relat_1(k5_relat_1(A_37, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.23  tff(c_160, plain, (![A_10, B_36]: (k2_relat_1(k5_relat_1(k6_relat_1(A_10), B_36))=k9_relat_1(B_36, A_10) | ~v1_relat_1(B_36) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_140])).
% 2.00/1.23  tff(c_170, plain, (![A_38, B_39]: (k2_relat_1(k5_relat_1(k6_relat_1(A_38), B_39))=k9_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 2.00/1.23  tff(c_182, plain, (![A_14, B_15]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_14, B_15)))=k9_relat_1(k6_relat_1(A_14), B_15) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_170])).
% 2.00/1.23  tff(c_186, plain, (![A_14, B_15]: (k9_relat_1(k6_relat_1(A_14), B_15)=k3_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_182])).
% 2.00/1.23  tff(c_24, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.00/1.23  tff(c_205, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_24])).
% 2.00/1.23  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.00/1.23  tff(c_80, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.23  tff(c_84, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_80])).
% 2.00/1.23  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.23  tff(c_108, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.23  tff(c_111, plain, (![A_10, A_31]: (k7_relat_1(k6_relat_1(A_10), A_31)=k6_relat_1(A_10) | ~r1_tarski(A_10, A_31) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_108])).
% 2.00/1.23  tff(c_114, plain, (![A_32, A_33]: (k7_relat_1(k6_relat_1(A_32), A_33)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_111])).
% 2.00/1.23  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.23  tff(c_120, plain, (![A_32, A_33]: (k9_relat_1(k6_relat_1(A_32), A_33)=k2_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)) | ~r1_tarski(A_32, A_33))), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 2.00/1.23  tff(c_126, plain, (![A_32, A_33]: (k9_relat_1(k6_relat_1(A_32), A_33)=A_32 | ~r1_tarski(A_32, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_120])).
% 2.00/1.23  tff(c_227, plain, (![A_45, A_46]: (k3_xboole_0(A_45, A_46)=A_45 | ~r1_tarski(A_45, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_126])).
% 2.00/1.23  tff(c_231, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_84, c_227])).
% 2.00/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.23  tff(c_235, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_231, c_2])).
% 2.00/1.23  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_235])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.24  #Sup     : 50
% 2.00/1.24  #Fact    : 0
% 2.00/1.24  #Define  : 0
% 2.00/1.24  #Split   : 1
% 2.00/1.24  #Chain   : 0
% 2.00/1.24  #Close   : 0
% 2.00/1.24  
% 2.00/1.24  Ordering : KBO
% 2.00/1.24  
% 2.00/1.24  Simplification rules
% 2.00/1.24  ----------------------
% 2.00/1.24  #Subsume      : 0
% 2.00/1.24  #Demod        : 13
% 2.00/1.24  #Tautology    : 30
% 2.00/1.24  #SimpNegUnit  : 1
% 2.00/1.24  #BackRed      : 2
% 2.00/1.24  
% 2.00/1.24  #Partial instantiations: 0
% 2.00/1.24  #Strategies tried      : 1
% 2.00/1.24  
% 2.00/1.24  Timing (in seconds)
% 2.00/1.24  ----------------------
% 2.00/1.24  Preprocessing        : 0.29
% 2.00/1.24  Parsing              : 0.16
% 2.00/1.24  CNF conversion       : 0.02
% 2.00/1.24  Main loop            : 0.16
% 2.00/1.24  Inferencing          : 0.07
% 2.00/1.24  Reduction            : 0.05
% 2.00/1.24  Demodulation         : 0.04
% 2.00/1.24  BG Simplification    : 0.01
% 2.00/1.24  Subsumption          : 0.02
% 2.00/1.24  Abstraction          : 0.01
% 2.00/1.24  MUC search           : 0.00
% 2.00/1.24  Cooper               : 0.00
% 2.00/1.24  Total                : 0.48
% 2.00/1.24  Index Insertion      : 0.00
% 2.00/1.24  Index Deletion       : 0.00
% 2.00/1.24  Index Matching       : 0.00
% 2.00/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
