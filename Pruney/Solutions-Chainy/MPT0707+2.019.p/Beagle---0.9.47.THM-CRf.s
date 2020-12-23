%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:18 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  71 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [B_29,A_30] : k5_relat_1(k6_relat_1(B_29),k6_relat_1(A_30)) = k6_relat_1(k3_xboole_0(A_30,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,(
    ! [A_30,B_29] :
      ( k7_relat_1(k6_relat_1(A_30),B_29) = k6_relat_1(k3_xboole_0(A_30,B_29))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_128,plain,(
    ! [A_31,B_32] : k7_relat_1(k6_relat_1(A_31),B_32) = k6_relat_1(k3_xboole_0(A_31,B_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_114])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_31,B_32] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_31,B_32))) = k9_relat_1(k6_relat_1(A_31),B_32)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_140,plain,(
    ! [A_31,B_32] : k9_relat_1(k6_relat_1(A_31),B_32) = k3_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12,c_134])).

tff(c_24,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_81,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_14,A_13] : k5_relat_1(k6_relat_1(B_14),k6_relat_1(A_13)) = k6_relat_1(k3_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = B_36
      | ~ r1_tarski(k1_relat_1(B_36),A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_35,A_7] :
      ( k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_7)) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_35)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_159,plain,(
    ! [A_37,A_38] :
      ( k6_relat_1(k3_xboole_0(A_37,A_38)) = k6_relat_1(A_37)
      | ~ r1_tarski(A_37,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22,c_155])).

tff(c_180,plain,(
    ! [A_37,A_38] :
      ( k3_xboole_0(A_37,A_38) = k1_relat_1(k6_relat_1(A_37))
      | ~ r1_tarski(A_37,A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_10])).

tff(c_261,plain,(
    ! [A_41,A_42] :
      ( k3_xboole_0(A_41,A_42) = A_41
      | ~ r1_tarski(A_41,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_180])).

tff(c_265,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_89,c_261])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_275,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_2])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.96/1.28  
% 1.96/1.28  %Foreground sorts:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Background operators:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Foreground operators:
% 1.96/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.28  
% 1.96/1.29  tff(f_53, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.96/1.29  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.96/1.29  tff(f_55, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.96/1.29  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.96/1.29  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.96/1.29  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.96/1.29  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.96/1.29  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 1.96/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.96/1.29  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.29  tff(c_12, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.29  tff(c_108, plain, (![B_29, A_30]: (k5_relat_1(k6_relat_1(B_29), k6_relat_1(A_30))=k6_relat_1(k3_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.29  tff(c_16, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.29  tff(c_114, plain, (![A_30, B_29]: (k7_relat_1(k6_relat_1(A_30), B_29)=k6_relat_1(k3_xboole_0(A_30, B_29)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 1.96/1.29  tff(c_128, plain, (![A_31, B_32]: (k7_relat_1(k6_relat_1(A_31), B_32)=k6_relat_1(k3_xboole_0(A_31, B_32)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_114])).
% 1.96/1.29  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.29  tff(c_134, plain, (![A_31, B_32]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_31, B_32)))=k9_relat_1(k6_relat_1(A_31), B_32) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 1.96/1.29  tff(c_140, plain, (![A_31, B_32]: (k9_relat_1(k6_relat_1(A_31), B_32)=k3_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12, c_134])).
% 1.96/1.29  tff(c_24, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.29  tff(c_142, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_24])).
% 1.96/1.29  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.29  tff(c_81, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.29  tff(c_89, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_81])).
% 1.96/1.29  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.29  tff(c_22, plain, (![B_14, A_13]: (k5_relat_1(k6_relat_1(B_14), k6_relat_1(A_13))=k6_relat_1(k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.29  tff(c_152, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=B_36 | ~r1_tarski(k1_relat_1(B_36), A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.29  tff(c_155, plain, (![A_35, A_7]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_7))=k6_relat_1(A_7) | ~r1_tarski(A_7, A_35) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_152])).
% 1.96/1.29  tff(c_159, plain, (![A_37, A_38]: (k6_relat_1(k3_xboole_0(A_37, A_38))=k6_relat_1(A_37) | ~r1_tarski(A_37, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22, c_155])).
% 1.96/1.29  tff(c_180, plain, (![A_37, A_38]: (k3_xboole_0(A_37, A_38)=k1_relat_1(k6_relat_1(A_37)) | ~r1_tarski(A_37, A_38))), inference(superposition, [status(thm), theory('equality')], [c_159, c_10])).
% 1.96/1.29  tff(c_261, plain, (![A_41, A_42]: (k3_xboole_0(A_41, A_42)=A_41 | ~r1_tarski(A_41, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_180])).
% 1.96/1.29  tff(c_265, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_89, c_261])).
% 1.96/1.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.29  tff(c_275, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_265, c_2])).
% 1.96/1.29  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_275])).
% 1.96/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  Inference rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Ref     : 0
% 1.96/1.29  #Sup     : 65
% 1.96/1.29  #Fact    : 0
% 1.96/1.29  #Define  : 0
% 1.96/1.29  #Split   : 0
% 1.96/1.29  #Chain   : 0
% 1.96/1.29  #Close   : 0
% 1.96/1.29  
% 1.96/1.29  Ordering : KBO
% 1.96/1.29  
% 1.96/1.29  Simplification rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Subsume      : 2
% 1.96/1.29  #Demod        : 25
% 1.96/1.29  #Tautology    : 34
% 1.96/1.29  #SimpNegUnit  : 1
% 1.96/1.29  #BackRed      : 1
% 1.96/1.29  
% 1.96/1.29  #Partial instantiations: 0
% 1.96/1.29  #Strategies tried      : 1
% 1.96/1.29  
% 1.96/1.29  Timing (in seconds)
% 1.96/1.29  ----------------------
% 1.96/1.29  Preprocessing        : 0.30
% 1.96/1.29  Parsing              : 0.17
% 1.96/1.29  CNF conversion       : 0.02
% 1.96/1.29  Main loop            : 0.19
% 1.96/1.29  Inferencing          : 0.08
% 1.96/1.29  Reduction            : 0.07
% 1.96/1.29  Demodulation         : 0.05
% 1.96/1.29  BG Simplification    : 0.01
% 1.96/1.29  Subsumption          : 0.03
% 1.96/1.29  Abstraction          : 0.01
% 1.96/1.29  MUC search           : 0.00
% 1.96/1.29  Cooper               : 0.00
% 1.96/1.29  Total                : 0.52
% 1.96/1.29  Index Insertion      : 0.00
% 1.96/1.29  Index Deletion       : 0.00
% 1.96/1.29  Index Matching       : 0.00
% 1.96/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
