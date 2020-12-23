%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:19 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 104 expanded)
%              Number of equality atoms :   35 (  48 expanded)
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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( k7_relat_1(B,A) = k7_relat_1(C,A)
           => k9_relat_1(B,A) = k9_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_51,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [B_30,A_31] :
      ( k5_relat_1(B_30,k6_relat_1(A_31)) = B_30
      | ~ r1_tarski(k2_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [A_11,A_31] :
      ( k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_31)) = k6_relat_1(A_11)
      | ~ r1_tarski(A_11,A_31)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_103])).

tff(c_174,plain,(
    ! [A_38,A_39] :
      ( k5_relat_1(k6_relat_1(A_38),k6_relat_1(A_39)) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_106])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_188,plain,(
    ! [A_39,A_38] :
      ( k7_relat_1(k6_relat_1(A_39),A_38) = k6_relat_1(A_38)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_24])).

tff(c_211,plain,(
    ! [A_39,A_38] :
      ( k7_relat_1(k6_relat_1(A_39),A_38) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_188])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_32] :
      ( k5_relat_1(B_32,k6_relat_1(k2_relat_1(B_32))) = B_32
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_121,plain,(
    ! [A_14] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_14))),A_14) = k6_relat_1(A_14)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_14))))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_24])).

tff(c_134,plain,(
    ! [A_14] : k7_relat_1(k6_relat_1(A_14),A_14) = k6_relat_1(A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_20,c_121])).

tff(c_150,plain,(
    ! [C_34,A_35,B_36] :
      ( k9_relat_1(C_34,A_35) = k9_relat_1(B_36,A_35)
      | k7_relat_1(C_34,A_35) != k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_243,plain,(
    ! [A_42,A_43,B_44] :
      ( k9_relat_1(k6_relat_1(A_42),A_43) = k9_relat_1(B_44,A_43)
      | k7_relat_1(k6_relat_1(A_42),A_43) != k7_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_247,plain,(
    ! [A_47,A_46,A_45] :
      ( k9_relat_1(k6_relat_1(A_47),A_46) = k9_relat_1(k6_relat_1(A_45),A_46)
      | k7_relat_1(k6_relat_1(A_47),A_46) != k7_relat_1(k6_relat_1(A_45),A_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_243])).

tff(c_18,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    ! [A_26] :
      ( k9_relat_1(A_26,k1_relat_1(A_26)) = k2_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_11] :
      ( k9_relat_1(k6_relat_1(A_11),A_11) = k2_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_71])).

tff(c_84,plain,(
    ! [A_11] : k9_relat_1(k6_relat_1(A_11),A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20,c_80])).

tff(c_263,plain,(
    ! [A_47,A_46] :
      ( k9_relat_1(k6_relat_1(A_47),A_46) = A_46
      | k7_relat_1(k6_relat_1(A_47),A_46) != k7_relat_1(k6_relat_1(A_46),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_84])).

tff(c_320,plain,(
    ! [A_48,A_49] :
      ( k9_relat_1(k6_relat_1(A_48),A_49) = A_49
      | k7_relat_1(k6_relat_1(A_48),A_49) != k6_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_263])).

tff(c_26,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_363,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_26])).

tff(c_372,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_363])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.35  
% 2.19/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.19/1.35  
% 2.19/1.35  %Foreground sorts:
% 2.19/1.35  
% 2.19/1.35  
% 2.19/1.35  %Background operators:
% 2.19/1.35  
% 2.19/1.35  
% 2.19/1.35  %Foreground operators:
% 2.19/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.19/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.19/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.19/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.19/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.35  
% 2.19/1.36  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.19/1.36  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.36  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.19/1.36  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.19/1.36  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.19/1.36  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.19/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.19/1.36  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k7_relat_1(B, A) = k7_relat_1(C, A)) => (k9_relat_1(B, A) = k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_relat_1)).
% 2.19/1.36  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.19/1.36  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.36  tff(c_51, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.36  tff(c_59, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.19/1.36  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.36  tff(c_20, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.36  tff(c_103, plain, (![B_30, A_31]: (k5_relat_1(B_30, k6_relat_1(A_31))=B_30 | ~r1_tarski(k2_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.36  tff(c_106, plain, (![A_11, A_31]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_31))=k6_relat_1(A_11) | ~r1_tarski(A_11, A_31) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_103])).
% 2.19/1.36  tff(c_174, plain, (![A_38, A_39]: (k5_relat_1(k6_relat_1(A_38), k6_relat_1(A_39))=k6_relat_1(A_38) | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_106])).
% 2.19/1.36  tff(c_24, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.36  tff(c_188, plain, (![A_39, A_38]: (k7_relat_1(k6_relat_1(A_39), A_38)=k6_relat_1(A_38) | ~v1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_38, A_39))), inference(superposition, [status(thm), theory('equality')], [c_174, c_24])).
% 2.19/1.36  tff(c_211, plain, (![A_39, A_38]: (k7_relat_1(k6_relat_1(A_39), A_38)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_188])).
% 2.19/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.36  tff(c_114, plain, (![B_32]: (k5_relat_1(B_32, k6_relat_1(k2_relat_1(B_32)))=B_32 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_6, c_103])).
% 2.19/1.36  tff(c_121, plain, (![A_14]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_14))), A_14)=k6_relat_1(A_14) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_14)))) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_24])).
% 2.19/1.36  tff(c_134, plain, (![A_14]: (k7_relat_1(k6_relat_1(A_14), A_14)=k6_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_20, c_121])).
% 2.19/1.36  tff(c_150, plain, (![C_34, A_35, B_36]: (k9_relat_1(C_34, A_35)=k9_relat_1(B_36, A_35) | k7_relat_1(C_34, A_35)!=k7_relat_1(B_36, A_35) | ~v1_relat_1(C_34) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.36  tff(c_243, plain, (![A_42, A_43, B_44]: (k9_relat_1(k6_relat_1(A_42), A_43)=k9_relat_1(B_44, A_43) | k7_relat_1(k6_relat_1(A_42), A_43)!=k7_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_12, c_150])).
% 2.19/1.36  tff(c_247, plain, (![A_47, A_46, A_45]: (k9_relat_1(k6_relat_1(A_47), A_46)=k9_relat_1(k6_relat_1(A_45), A_46) | k7_relat_1(k6_relat_1(A_47), A_46)!=k7_relat_1(k6_relat_1(A_45), A_46))), inference(resolution, [status(thm)], [c_12, c_243])).
% 2.19/1.36  tff(c_18, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.36  tff(c_71, plain, (![A_26]: (k9_relat_1(A_26, k1_relat_1(A_26))=k2_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.36  tff(c_80, plain, (![A_11]: (k9_relat_1(k6_relat_1(A_11), A_11)=k2_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_71])).
% 2.19/1.36  tff(c_84, plain, (![A_11]: (k9_relat_1(k6_relat_1(A_11), A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20, c_80])).
% 2.19/1.36  tff(c_263, plain, (![A_47, A_46]: (k9_relat_1(k6_relat_1(A_47), A_46)=A_46 | k7_relat_1(k6_relat_1(A_47), A_46)!=k7_relat_1(k6_relat_1(A_46), A_46))), inference(superposition, [status(thm), theory('equality')], [c_247, c_84])).
% 2.19/1.36  tff(c_320, plain, (![A_48, A_49]: (k9_relat_1(k6_relat_1(A_48), A_49)=A_49 | k7_relat_1(k6_relat_1(A_48), A_49)!=k6_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_263])).
% 2.19/1.36  tff(c_26, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.36  tff(c_363, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_320, c_26])).
% 2.19/1.36  tff(c_372, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_211, c_363])).
% 2.19/1.36  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_372])).
% 2.19/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.36  
% 2.19/1.36  Inference rules
% 2.19/1.36  ----------------------
% 2.19/1.36  #Ref     : 0
% 2.19/1.36  #Sup     : 72
% 2.19/1.36  #Fact    : 0
% 2.19/1.36  #Define  : 0
% 2.19/1.36  #Split   : 1
% 2.19/1.36  #Chain   : 0
% 2.19/1.36  #Close   : 0
% 2.19/1.36  
% 2.19/1.36  Ordering : KBO
% 2.19/1.36  
% 2.19/1.36  Simplification rules
% 2.19/1.36  ----------------------
% 2.19/1.36  #Subsume      : 1
% 2.19/1.36  #Demod        : 72
% 2.19/1.36  #Tautology    : 38
% 2.19/1.36  #SimpNegUnit  : 0
% 2.19/1.36  #BackRed      : 0
% 2.19/1.36  
% 2.19/1.36  #Partial instantiations: 0
% 2.19/1.36  #Strategies tried      : 1
% 2.19/1.36  
% 2.19/1.36  Timing (in seconds)
% 2.19/1.36  ----------------------
% 2.19/1.36  Preprocessing        : 0.31
% 2.19/1.36  Parsing              : 0.17
% 2.19/1.36  CNF conversion       : 0.02
% 2.19/1.36  Main loop            : 0.22
% 2.19/1.36  Inferencing          : 0.09
% 2.19/1.36  Reduction            : 0.06
% 2.19/1.36  Demodulation         : 0.05
% 2.19/1.36  BG Simplification    : 0.01
% 2.19/1.36  Subsumption          : 0.04
% 2.19/1.36  Abstraction          : 0.01
% 2.19/1.36  MUC search           : 0.00
% 2.19/1.36  Cooper               : 0.00
% 2.19/1.36  Total                : 0.55
% 2.19/1.36  Index Insertion      : 0.00
% 2.19/1.36  Index Deletion       : 0.00
% 2.19/1.36  Index Matching       : 0.00
% 2.19/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
