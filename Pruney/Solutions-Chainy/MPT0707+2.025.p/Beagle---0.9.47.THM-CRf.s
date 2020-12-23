%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:19 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  74 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_54,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_12,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [B_13,A_12] : k5_relat_1(k6_relat_1(B_13),k6_relat_1(A_12)) = k6_relat_1(k3_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = B_27
      | ~ r1_tarski(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [A_26,A_8] :
      ( k5_relat_1(k6_relat_1(A_26),k6_relat_1(A_8)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_26)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_103,plain,(
    ! [A_28,A_29] :
      ( k6_relat_1(k3_xboole_0(A_28,A_29)) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_100])).

tff(c_115,plain,(
    ! [A_28,A_29] :
      ( k3_xboole_0(A_28,A_29) = k2_relat_1(k6_relat_1(A_28))
      | ~ r1_tarski(A_28,A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_140,plain,(
    ! [A_30,A_31] :
      ( k3_xboole_0(A_30,A_31) = A_30
      | ~ r1_tarski(A_30,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_144,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_87,c_140])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2])).

tff(c_167,plain,(
    ! [B_32,A_33] :
      ( k9_relat_1(B_32,k2_relat_1(A_33)) = k2_relat_1(k5_relat_1(A_33,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_176,plain,(
    ! [A_8,B_32] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_8),B_32)) = k9_relat_1(B_32,A_8)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_250,plain,(
    ! [A_38,B_39] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_38),B_39)) = k9_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_176])).

tff(c_268,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_12,B_13))) = k9_relat_1(k6_relat_1(A_12),B_13)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_250])).

tff(c_272,plain,(
    ! [A_12,B_13] : k9_relat_1(k6_relat_1(A_12),B_13) = k3_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_268])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_273,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_22])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.33  
% 1.94/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.33  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.94/1.33  
% 1.94/1.33  %Foreground sorts:
% 1.94/1.33  
% 1.94/1.33  
% 1.94/1.33  %Background operators:
% 1.94/1.33  
% 1.94/1.33  
% 1.94/1.33  %Foreground operators:
% 1.94/1.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.94/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.94/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.33  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.94/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.33  
% 1.94/1.34  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.94/1.34  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.94/1.34  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.94/1.34  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.94/1.34  tff(f_54, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.94/1.34  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.94/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.94/1.34  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.94/1.34  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.34  tff(c_79, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.34  tff(c_87, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_79])).
% 1.94/1.34  tff(c_12, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.34  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.34  tff(c_20, plain, (![B_13, A_12]: (k5_relat_1(k6_relat_1(B_13), k6_relat_1(A_12))=k6_relat_1(k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.34  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.34  tff(c_97, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=B_27 | ~r1_tarski(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.34  tff(c_100, plain, (![A_26, A_8]: (k5_relat_1(k6_relat_1(A_26), k6_relat_1(A_8))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_26) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_97])).
% 1.94/1.34  tff(c_103, plain, (![A_28, A_29]: (k6_relat_1(k3_xboole_0(A_28, A_29))=k6_relat_1(A_28) | ~r1_tarski(A_28, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_100])).
% 1.94/1.34  tff(c_115, plain, (![A_28, A_29]: (k3_xboole_0(A_28, A_29)=k2_relat_1(k6_relat_1(A_28)) | ~r1_tarski(A_28, A_29))), inference(superposition, [status(thm), theory('equality')], [c_103, c_12])).
% 1.94/1.34  tff(c_140, plain, (![A_30, A_31]: (k3_xboole_0(A_30, A_31)=A_30 | ~r1_tarski(A_30, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_115])).
% 1.94/1.34  tff(c_144, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_87, c_140])).
% 1.94/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.34  tff(c_151, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_144, c_2])).
% 1.94/1.34  tff(c_167, plain, (![B_32, A_33]: (k9_relat_1(B_32, k2_relat_1(A_33))=k2_relat_1(k5_relat_1(A_33, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.34  tff(c_176, plain, (![A_8, B_32]: (k2_relat_1(k5_relat_1(k6_relat_1(A_8), B_32))=k9_relat_1(B_32, A_8) | ~v1_relat_1(B_32) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_167])).
% 1.94/1.34  tff(c_250, plain, (![A_38, B_39]: (k2_relat_1(k5_relat_1(k6_relat_1(A_38), B_39))=k9_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_176])).
% 1.94/1.34  tff(c_268, plain, (![A_12, B_13]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_12, B_13)))=k9_relat_1(k6_relat_1(A_12), B_13) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_250])).
% 1.94/1.34  tff(c_272, plain, (![A_12, B_13]: (k9_relat_1(k6_relat_1(A_12), B_13)=k3_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12, c_268])).
% 1.94/1.34  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.34  tff(c_273, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_272, c_22])).
% 1.94/1.34  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_273])).
% 1.94/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.34  
% 1.94/1.34  Inference rules
% 1.94/1.34  ----------------------
% 1.94/1.34  #Ref     : 0
% 1.94/1.34  #Sup     : 62
% 1.94/1.34  #Fact    : 0
% 1.94/1.34  #Define  : 0
% 1.94/1.34  #Split   : 1
% 1.94/1.34  #Chain   : 0
% 1.94/1.34  #Close   : 0
% 1.94/1.34  
% 1.94/1.34  Ordering : KBO
% 1.94/1.34  
% 1.94/1.34  Simplification rules
% 1.94/1.34  ----------------------
% 1.94/1.34  #Subsume      : 4
% 1.94/1.34  #Demod        : 25
% 1.94/1.34  #Tautology    : 37
% 1.94/1.34  #SimpNegUnit  : 0
% 1.94/1.34  #BackRed      : 1
% 1.94/1.34  
% 1.94/1.34  #Partial instantiations: 0
% 1.94/1.34  #Strategies tried      : 1
% 1.94/1.34  
% 1.94/1.34  Timing (in seconds)
% 1.94/1.34  ----------------------
% 1.94/1.35  Preprocessing        : 0.33
% 1.94/1.35  Parsing              : 0.17
% 1.94/1.35  CNF conversion       : 0.02
% 1.94/1.35  Main loop            : 0.18
% 1.94/1.35  Inferencing          : 0.06
% 1.94/1.35  Reduction            : 0.07
% 1.94/1.35  Demodulation         : 0.05
% 1.94/1.35  BG Simplification    : 0.01
% 1.94/1.35  Subsumption          : 0.03
% 1.94/1.35  Abstraction          : 0.01
% 1.94/1.35  MUC search           : 0.00
% 1.94/1.35  Cooper               : 0.00
% 1.94/1.35  Total                : 0.55
% 1.94/1.35  Index Insertion      : 0.00
% 1.94/1.35  Index Deletion       : 0.00
% 1.94/1.35  Index Matching       : 0.00
% 1.94/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
