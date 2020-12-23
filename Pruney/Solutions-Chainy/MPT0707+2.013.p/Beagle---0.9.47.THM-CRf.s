%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:17 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  68 expanded)
%              Number of equality atoms :   28 (  38 expanded)
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

tff(f_53,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

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

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [B_26,A_27] : k5_relat_1(k6_relat_1(B_26),k6_relat_1(A_27)) = k6_relat_1(k3_xboole_0(A_27,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    ! [A_27,B_26] :
      ( k7_relat_1(k6_relat_1(A_27),B_26) = k6_relat_1(k3_xboole_0(A_27,B_26))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_18])).

tff(c_112,plain,(
    ! [A_27,B_26] : k7_relat_1(k6_relat_1(A_27),B_26) = k6_relat_1(k3_xboole_0(A_27,B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_102])).

tff(c_126,plain,(
    ! [B_30,A_31] :
      ( k2_relat_1(k7_relat_1(B_30,A_31)) = k9_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [A_27,B_26] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_27,B_26))) = k9_relat_1(k6_relat_1(A_27),B_26)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_126])).

tff(c_139,plain,(
    ! [A_27,B_26] : k9_relat_1(k6_relat_1(A_27),B_26) = k3_xboole_0(A_27,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_135])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_22])).

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

tff(c_20,plain,(
    ! [B_14,A_13] : k5_relat_1(k6_relat_1(B_14),k6_relat_1(A_13)) = k6_relat_1(k3_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [A_34,A_8] :
      ( k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_8)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_34)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_150])).

tff(c_156,plain,(
    ! [A_36,A_37] :
      ( k6_relat_1(k3_xboole_0(A_36,A_37)) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20,c_153])).

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
    inference(negUnitSimplification,[status(thm)],[c_140,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.99/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.23  
% 1.99/1.24  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.99/1.24  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.99/1.24  tff(f_53, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.99/1.24  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.99/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.99/1.24  tff(f_58, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.99/1.24  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.24  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 1.99/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.24  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.24  tff(c_14, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.24  tff(c_96, plain, (![B_26, A_27]: (k5_relat_1(k6_relat_1(B_26), k6_relat_1(A_27))=k6_relat_1(k3_xboole_0(A_27, B_26)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.24  tff(c_18, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.24  tff(c_102, plain, (![A_27, B_26]: (k7_relat_1(k6_relat_1(A_27), B_26)=k6_relat_1(k3_xboole_0(A_27, B_26)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_18])).
% 1.99/1.24  tff(c_112, plain, (![A_27, B_26]: (k7_relat_1(k6_relat_1(A_27), B_26)=k6_relat_1(k3_xboole_0(A_27, B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_102])).
% 1.99/1.24  tff(c_126, plain, (![B_30, A_31]: (k2_relat_1(k7_relat_1(B_30, A_31))=k9_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.24  tff(c_135, plain, (![A_27, B_26]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_27, B_26)))=k9_relat_1(k6_relat_1(A_27), B_26) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_126])).
% 1.99/1.24  tff(c_139, plain, (![A_27, B_26]: (k9_relat_1(k6_relat_1(A_27), B_26)=k3_xboole_0(A_27, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_135])).
% 1.99/1.24  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.24  tff(c_140, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_22])).
% 1.99/1.24  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.24  tff(c_77, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.24  tff(c_81, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_77])).
% 1.99/1.24  tff(c_12, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.24  tff(c_20, plain, (![B_14, A_13]: (k5_relat_1(k6_relat_1(B_14), k6_relat_1(A_13))=k6_relat_1(k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.24  tff(c_150, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.24  tff(c_153, plain, (![A_34, A_8]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_8))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_34) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_150])).
% 1.99/1.24  tff(c_156, plain, (![A_36, A_37]: (k6_relat_1(k3_xboole_0(A_36, A_37))=k6_relat_1(A_36) | ~r1_tarski(A_36, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20, c_153])).
% 1.99/1.24  tff(c_177, plain, (![A_36, A_37]: (k3_xboole_0(A_36, A_37)=k1_relat_1(k6_relat_1(A_36)) | ~r1_tarski(A_36, A_37))), inference(superposition, [status(thm), theory('equality')], [c_156, c_12])).
% 1.99/1.24  tff(c_201, plain, (![A_38, A_39]: (k3_xboole_0(A_38, A_39)=A_38 | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_177])).
% 1.99/1.24  tff(c_205, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_81, c_201])).
% 1.99/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.24  tff(c_212, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 1.99/1.24  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_212])).
% 1.99/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  Inference rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Ref     : 0
% 1.99/1.24  #Sup     : 48
% 1.99/1.24  #Fact    : 0
% 1.99/1.24  #Define  : 0
% 1.99/1.24  #Split   : 0
% 1.99/1.24  #Chain   : 0
% 1.99/1.24  #Close   : 0
% 1.99/1.24  
% 1.99/1.24  Ordering : KBO
% 1.99/1.24  
% 1.99/1.24  Simplification rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Subsume      : 0
% 1.99/1.24  #Demod        : 16
% 1.99/1.24  #Tautology    : 29
% 1.99/1.24  #SimpNegUnit  : 1
% 1.99/1.24  #BackRed      : 1
% 1.99/1.24  
% 1.99/1.24  #Partial instantiations: 0
% 1.99/1.24  #Strategies tried      : 1
% 1.99/1.24  
% 1.99/1.24  Timing (in seconds)
% 1.99/1.24  ----------------------
% 1.99/1.24  Preprocessing        : 0.29
% 1.99/1.24  Parsing              : 0.17
% 1.99/1.24  CNF conversion       : 0.02
% 1.99/1.24  Main loop            : 0.16
% 1.99/1.24  Inferencing          : 0.06
% 1.99/1.24  Reduction            : 0.05
% 1.99/1.24  Demodulation         : 0.04
% 1.99/1.24  BG Simplification    : 0.01
% 1.99/1.24  Subsumption          : 0.02
% 1.99/1.24  Abstraction          : 0.01
% 1.99/1.24  MUC search           : 0.00
% 1.99/1.24  Cooper               : 0.00
% 1.99/1.25  Total                : 0.47
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
