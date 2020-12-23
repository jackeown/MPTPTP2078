%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 (  96 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( k7_relat_1(B,A) = k7_relat_1(C,A)
           => k9_relat_1(B,A) = k9_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_45,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_142,plain,(
    ! [B_29,A_30] :
      ( k5_relat_1(B_29,k6_relat_1(A_30)) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    ! [A_9,A_30] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_30)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_30)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_150,plain,(
    ! [A_31,A_32] :
      ( k5_relat_1(k6_relat_1(A_31),k6_relat_1(A_32)) = k6_relat_1(A_31)
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_145])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_156,plain,(
    ! [A_32,A_31] :
      ( k7_relat_1(k6_relat_1(A_32),A_31) = k6_relat_1(A_31)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_20])).

tff(c_181,plain,(
    ! [A_32,A_31] :
      ( k7_relat_1(k6_relat_1(A_32),A_31) = k6_relat_1(A_31)
      | ~ r1_tarski(A_31,A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_156])).

tff(c_100,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_relat_1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_111,plain,(
    ! [A_26] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_26))),A_26) = k6_relat_1(A_26)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_26)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_126,plain,(
    ! [A_26] : k7_relat_1(k6_relat_1(A_26),A_26) = k6_relat_1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_14,c_111])).

tff(c_193,plain,(
    ! [C_33,A_34,B_35] :
      ( k9_relat_1(C_33,A_34) = k9_relat_1(B_35,A_34)
      | k7_relat_1(C_33,A_34) != k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    ! [A_38,A_39,B_40] :
      ( k9_relat_1(k6_relat_1(A_38),A_39) = k9_relat_1(B_40,A_39)
      | k7_relat_1(k6_relat_1(A_38),A_39) != k7_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_219,plain,(
    ! [A_43,A_42,A_41] :
      ( k9_relat_1(k6_relat_1(A_43),A_42) = k9_relat_1(k6_relat_1(A_41),A_42)
      | k7_relat_1(k6_relat_1(A_43),A_42) != k7_relat_1(k6_relat_1(A_41),A_42) ) ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_9] :
      ( k9_relat_1(k6_relat_1(A_9),A_9) = k2_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_67,plain,(
    ! [A_9] : k9_relat_1(k6_relat_1(A_9),A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14,c_63])).

tff(c_235,plain,(
    ! [A_43,A_42] :
      ( k9_relat_1(k6_relat_1(A_43),A_42) = A_42
      | k7_relat_1(k6_relat_1(A_43),A_42) != k7_relat_1(k6_relat_1(A_42),A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_67])).

tff(c_292,plain,(
    ! [A_44,A_45] :
      ( k9_relat_1(k6_relat_1(A_44),A_45) = A_45
      | k7_relat_1(k6_relat_1(A_44),A_45) != k6_relat_1(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_235])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_335,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_22])).

tff(c_344,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_335])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.25/1.32  
% 2.25/1.32  %Foreground sorts:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Background operators:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Foreground operators:
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.25/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.32  
% 2.25/1.34  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.25/1.34  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.34  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.25/1.34  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.25/1.34  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.25/1.34  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.25/1.34  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.25/1.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k7_relat_1(B, A) = k7_relat_1(C, A)) => (k9_relat_1(B, A) = k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_relat_1)).
% 2.25/1.34  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.25/1.34  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_45, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.34  tff(c_53, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.25/1.34  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.34  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.34  tff(c_142, plain, (![B_29, A_30]: (k5_relat_1(B_29, k6_relat_1(A_30))=B_29 | ~r1_tarski(k2_relat_1(B_29), A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.25/1.34  tff(c_145, plain, (![A_9, A_30]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_30))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_30) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_142])).
% 2.25/1.34  tff(c_150, plain, (![A_31, A_32]: (k5_relat_1(k6_relat_1(A_31), k6_relat_1(A_32))=k6_relat_1(A_31) | ~r1_tarski(A_31, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_145])).
% 2.25/1.34  tff(c_20, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.34  tff(c_156, plain, (![A_32, A_31]: (k7_relat_1(k6_relat_1(A_32), A_31)=k6_relat_1(A_31) | ~v1_relat_1(k6_relat_1(A_32)) | ~r1_tarski(A_31, A_32))), inference(superposition, [status(thm), theory('equality')], [c_150, c_20])).
% 2.25/1.34  tff(c_181, plain, (![A_32, A_31]: (k7_relat_1(k6_relat_1(A_32), A_31)=k6_relat_1(A_31) | ~r1_tarski(A_31, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_156])).
% 2.25/1.34  tff(c_100, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.34  tff(c_18, plain, (![A_12]: (k5_relat_1(A_12, k6_relat_1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.34  tff(c_111, plain, (![A_26]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_26))), A_26)=k6_relat_1(A_26) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_26)))))), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 2.25/1.34  tff(c_126, plain, (![A_26]: (k7_relat_1(k6_relat_1(A_26), A_26)=k6_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_14, c_111])).
% 2.25/1.34  tff(c_193, plain, (![C_33, A_34, B_35]: (k9_relat_1(C_33, A_34)=k9_relat_1(B_35, A_34) | k7_relat_1(C_33, A_34)!=k7_relat_1(B_35, A_34) | ~v1_relat_1(C_33) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.34  tff(c_215, plain, (![A_38, A_39, B_40]: (k9_relat_1(k6_relat_1(A_38), A_39)=k9_relat_1(B_40, A_39) | k7_relat_1(k6_relat_1(A_38), A_39)!=k7_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_6, c_193])).
% 2.25/1.34  tff(c_219, plain, (![A_43, A_42, A_41]: (k9_relat_1(k6_relat_1(A_43), A_42)=k9_relat_1(k6_relat_1(A_41), A_42) | k7_relat_1(k6_relat_1(A_43), A_42)!=k7_relat_1(k6_relat_1(A_41), A_42))), inference(resolution, [status(thm)], [c_6, c_215])).
% 2.25/1.34  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.34  tff(c_54, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.34  tff(c_63, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=k2_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_54])).
% 2.25/1.34  tff(c_67, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14, c_63])).
% 2.25/1.34  tff(c_235, plain, (![A_43, A_42]: (k9_relat_1(k6_relat_1(A_43), A_42)=A_42 | k7_relat_1(k6_relat_1(A_43), A_42)!=k7_relat_1(k6_relat_1(A_42), A_42))), inference(superposition, [status(thm), theory('equality')], [c_219, c_67])).
% 2.25/1.34  tff(c_292, plain, (![A_44, A_45]: (k9_relat_1(k6_relat_1(A_44), A_45)=A_45 | k7_relat_1(k6_relat_1(A_44), A_45)!=k6_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_235])).
% 2.25/1.34  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_335, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_292, c_22])).
% 2.25/1.34  tff(c_344, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_181, c_335])).
% 2.25/1.34  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_344])).
% 2.25/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.34  
% 2.25/1.34  Inference rules
% 2.25/1.34  ----------------------
% 2.25/1.34  #Ref     : 0
% 2.25/1.34  #Sup     : 69
% 2.25/1.34  #Fact    : 0
% 2.25/1.34  #Define  : 0
% 2.25/1.34  #Split   : 0
% 2.25/1.34  #Chain   : 0
% 2.25/1.34  #Close   : 0
% 2.25/1.34  
% 2.25/1.34  Ordering : KBO
% 2.25/1.34  
% 2.25/1.34  Simplification rules
% 2.25/1.34  ----------------------
% 2.25/1.34  #Subsume      : 2
% 2.25/1.34  #Demod        : 64
% 2.25/1.34  #Tautology    : 36
% 2.25/1.34  #SimpNegUnit  : 0
% 2.25/1.34  #BackRed      : 0
% 2.25/1.34  
% 2.25/1.34  #Partial instantiations: 0
% 2.25/1.34  #Strategies tried      : 1
% 2.25/1.34  
% 2.25/1.34  Timing (in seconds)
% 2.25/1.34  ----------------------
% 2.25/1.34  Preprocessing        : 0.29
% 2.25/1.34  Parsing              : 0.17
% 2.25/1.34  CNF conversion       : 0.02
% 2.25/1.34  Main loop            : 0.23
% 2.25/1.34  Inferencing          : 0.10
% 2.25/1.34  Reduction            : 0.07
% 2.25/1.34  Demodulation         : 0.05
% 2.25/1.34  BG Simplification    : 0.02
% 2.25/1.34  Subsumption          : 0.03
% 2.25/1.34  Abstraction          : 0.02
% 2.25/1.34  MUC search           : 0.00
% 2.25/1.34  Cooper               : 0.00
% 2.25/1.34  Total                : 0.55
% 2.25/1.34  Index Insertion      : 0.00
% 2.25/1.34  Index Deletion       : 0.00
% 2.25/1.34  Index Matching       : 0.00
% 2.25/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
