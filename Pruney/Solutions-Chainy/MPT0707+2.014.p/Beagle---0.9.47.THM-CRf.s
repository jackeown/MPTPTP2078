%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:18 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   50 (  67 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = k7_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [B_14,A_13] : k5_relat_1(k6_relat_1(B_14),k6_relat_1(A_13)) = k6_relat_1(k3_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [A_13,A_28] :
      ( k7_relat_1(k6_relat_1(A_13),A_28) = k6_relat_1(k3_xboole_0(A_13,A_28))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_20])).

tff(c_125,plain,(
    ! [A_30,A_31] : k7_relat_1(k6_relat_1(A_30),A_31) = k6_relat_1(k3_xboole_0(A_30,A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [A_30,A_31] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_30,A_31))) = k9_relat_1(k6_relat_1(A_30),A_31)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_10])).

tff(c_137,plain,(
    ! [A_30,A_31] : k9_relat_1(k6_relat_1(A_30),A_31) = k3_xboole_0(A_30,A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_131])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_22])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_12,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    ! [A_13,A_28] : k7_relat_1(k6_relat_1(A_13),A_28) = k6_relat_1(k3_xboole_0(A_13,A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_149,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = B_34
      | ~ r1_tarski(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [A_8,A_35] :
      ( k7_relat_1(k6_relat_1(A_8),A_35) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_35)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_149])).

tff(c_156,plain,(
    ! [A_36,A_37] :
      ( k6_relat_1(k3_xboole_0(A_36,A_37)) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_121,c_152])).

tff(c_177,plain,(
    ! [A_36,A_37] :
      ( k3_xboole_0(A_36,A_37) = k1_relat_1(k6_relat_1(A_36))
      | ~ r1_tarski(A_36,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_12])).

tff(c_201,plain,(
    ! [A_38,A_39] :
      ( k3_xboole_0(A_38,A_39) = A_38
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_177])).

tff(c_205,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_81,c_201])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.21  
% 1.88/1.22  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.88/1.22  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.88/1.22  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.88/1.22  tff(f_53, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.88/1.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.88/1.22  tff(f_58, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.88/1.22  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.88/1.22  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.88/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.88/1.22  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.22  tff(c_14, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.22  tff(c_105, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=k7_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_20, plain, (![B_14, A_13]: (k5_relat_1(k6_relat_1(B_14), k6_relat_1(A_13))=k6_relat_1(k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.22  tff(c_112, plain, (![A_13, A_28]: (k7_relat_1(k6_relat_1(A_13), A_28)=k6_relat_1(k3_xboole_0(A_13, A_28)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_20])).
% 1.88/1.22  tff(c_125, plain, (![A_30, A_31]: (k7_relat_1(k6_relat_1(A_30), A_31)=k6_relat_1(k3_xboole_0(A_30, A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 1.88/1.22  tff(c_10, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.22  tff(c_131, plain, (![A_30, A_31]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_30, A_31)))=k9_relat_1(k6_relat_1(A_30), A_31) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_10])).
% 1.88/1.22  tff(c_137, plain, (![A_30, A_31]: (k9_relat_1(k6_relat_1(A_30), A_31)=k3_xboole_0(A_30, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_131])).
% 1.88/1.22  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.22  tff(c_139, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_22])).
% 1.88/1.22  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.22  tff(c_77, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.22  tff(c_81, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_77])).
% 1.88/1.22  tff(c_12, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.22  tff(c_121, plain, (![A_13, A_28]: (k7_relat_1(k6_relat_1(A_13), A_28)=k6_relat_1(k3_xboole_0(A_13, A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 1.88/1.22  tff(c_149, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=B_34 | ~r1_tarski(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.22  tff(c_152, plain, (![A_8, A_35]: (k7_relat_1(k6_relat_1(A_8), A_35)=k6_relat_1(A_8) | ~r1_tarski(A_8, A_35) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_149])).
% 1.88/1.22  tff(c_156, plain, (![A_36, A_37]: (k6_relat_1(k3_xboole_0(A_36, A_37))=k6_relat_1(A_36) | ~r1_tarski(A_36, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_121, c_152])).
% 1.88/1.22  tff(c_177, plain, (![A_36, A_37]: (k3_xboole_0(A_36, A_37)=k1_relat_1(k6_relat_1(A_36)) | ~r1_tarski(A_36, A_37))), inference(superposition, [status(thm), theory('equality')], [c_156, c_12])).
% 1.88/1.22  tff(c_201, plain, (![A_38, A_39]: (k3_xboole_0(A_38, A_39)=A_38 | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_177])).
% 1.88/1.22  tff(c_205, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_81, c_201])).
% 1.88/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.22  tff(c_212, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 1.88/1.22  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_212])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 48
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 0
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 0
% 1.88/1.22  #Demod        : 16
% 1.88/1.22  #Tautology    : 29
% 1.88/1.22  #SimpNegUnit  : 1
% 1.88/1.22  #BackRed      : 1
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.22  Preprocessing        : 0.25
% 1.88/1.22  Parsing              : 0.14
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.16
% 1.88/1.22  Inferencing          : 0.07
% 1.88/1.22  Reduction            : 0.05
% 1.88/1.22  Demodulation         : 0.04
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.02
% 1.88/1.22  Abstraction          : 0.01
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.22  Cooper               : 0.00
% 1.88/1.22  Total                : 0.44
% 1.88/1.22  Index Insertion      : 0.00
% 1.88/1.22  Index Deletion       : 0.00
% 1.88/1.22  Index Matching       : 0.00
% 1.88/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
