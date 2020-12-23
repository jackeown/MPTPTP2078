%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 117 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_20,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_18] : v4_relat_1(k6_relat_1(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_69,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ v4_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [A_18] :
      ( k7_relat_1(k6_relat_1(A_18),A_18) = k6_relat_1(A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69])).

tff(c_76,plain,(
    ! [A_32] : k7_relat_1(k6_relat_1(A_32),A_32) = k6_relat_1(A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_72])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_32] :
      ( k9_relat_1(k6_relat_1(A_32),A_32) = k2_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_88,plain,(
    ! [A_32] : k9_relat_1(k6_relat_1(A_32),A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_82])).

tff(c_99,plain,(
    ! [B_34,A_35] :
      ( k5_relat_1(B_34,k6_relat_1(A_35)) = B_34
      | ~ r1_tarski(k2_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    ! [A_15,A_35] :
      ( k5_relat_1(k6_relat_1(A_15),k6_relat_1(A_35)) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_35)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_107,plain,(
    ! [A_15,A_35] :
      ( k5_relat_1(k6_relat_1(A_15),k6_relat_1(A_35)) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_227,plain,(
    ! [B_52,C_53,A_54] :
      ( k9_relat_1(k5_relat_1(B_52,C_53),A_54) = k9_relat_1(C_53,k9_relat_1(B_52,A_54))
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_236,plain,(
    ! [A_35,A_15,A_54] :
      ( k9_relat_1(k6_relat_1(A_35),k9_relat_1(k6_relat_1(A_15),A_54)) = k9_relat_1(k6_relat_1(A_15),A_54)
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ r1_tarski(A_15,A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_227])).

tff(c_361,plain,(
    ! [A_65,A_66,A_67] :
      ( k9_relat_1(k6_relat_1(A_65),k9_relat_1(k6_relat_1(A_66),A_67)) = k9_relat_1(k6_relat_1(A_66),A_67)
      | ~ r1_tarski(A_66,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_236])).

tff(c_403,plain,(
    ! [A_65,A_32] :
      ( k9_relat_1(k6_relat_1(A_65),A_32) = k9_relat_1(k6_relat_1(A_32),A_32)
      | ~ r1_tarski(A_32,A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_361])).

tff(c_413,plain,(
    ! [A_68,A_69] :
      ( k9_relat_1(k6_relat_1(A_68),A_69) = A_69
      | ~ r1_tarski(A_69,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_403])).

tff(c_26,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_440,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_26])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:14:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.24  
% 2.25/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.24  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.25/1.24  
% 2.25/1.24  %Foreground sorts:
% 2.25/1.24  
% 2.25/1.24  
% 2.25/1.24  %Background operators:
% 2.25/1.24  
% 2.25/1.24  
% 2.25/1.24  %Foreground operators:
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.25/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.25/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.25/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.24  
% 2.25/1.25  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.25/1.25  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.25  tff(f_71, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.25/1.25  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.25/1.25  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.25/1.25  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.25/1.25  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.25/1.25  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.25/1.25  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.25/1.25  tff(c_51, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.25  tff(c_59, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.25/1.25  tff(c_20, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.25/1.25  tff(c_16, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.25  tff(c_22, plain, (![A_18]: (v4_relat_1(k6_relat_1(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.25/1.25  tff(c_69, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~v4_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.25  tff(c_72, plain, (![A_18]: (k7_relat_1(k6_relat_1(A_18), A_18)=k6_relat_1(A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(resolution, [status(thm)], [c_22, c_69])).
% 2.25/1.25  tff(c_76, plain, (![A_32]: (k7_relat_1(k6_relat_1(A_32), A_32)=k6_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_72])).
% 2.25/1.25  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.25  tff(c_82, plain, (![A_32]: (k9_relat_1(k6_relat_1(A_32), A_32)=k2_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_6])).
% 2.25/1.25  tff(c_88, plain, (![A_32]: (k9_relat_1(k6_relat_1(A_32), A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_82])).
% 2.25/1.25  tff(c_99, plain, (![B_34, A_35]: (k5_relat_1(B_34, k6_relat_1(A_35))=B_34 | ~r1_tarski(k2_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.25/1.25  tff(c_105, plain, (![A_15, A_35]: (k5_relat_1(k6_relat_1(A_15), k6_relat_1(A_35))=k6_relat_1(A_15) | ~r1_tarski(A_15, A_35) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_99])).
% 2.25/1.25  tff(c_107, plain, (![A_15, A_35]: (k5_relat_1(k6_relat_1(A_15), k6_relat_1(A_35))=k6_relat_1(A_15) | ~r1_tarski(A_15, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_105])).
% 2.25/1.25  tff(c_227, plain, (![B_52, C_53, A_54]: (k9_relat_1(k5_relat_1(B_52, C_53), A_54)=k9_relat_1(C_53, k9_relat_1(B_52, A_54)) | ~v1_relat_1(C_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.25  tff(c_236, plain, (![A_35, A_15, A_54]: (k9_relat_1(k6_relat_1(A_35), k9_relat_1(k6_relat_1(A_15), A_54))=k9_relat_1(k6_relat_1(A_15), A_54) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_15)) | ~r1_tarski(A_15, A_35))), inference(superposition, [status(thm), theory('equality')], [c_107, c_227])).
% 2.25/1.25  tff(c_361, plain, (![A_65, A_66, A_67]: (k9_relat_1(k6_relat_1(A_65), k9_relat_1(k6_relat_1(A_66), A_67))=k9_relat_1(k6_relat_1(A_66), A_67) | ~r1_tarski(A_66, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_236])).
% 2.25/1.25  tff(c_403, plain, (![A_65, A_32]: (k9_relat_1(k6_relat_1(A_65), A_32)=k9_relat_1(k6_relat_1(A_32), A_32) | ~r1_tarski(A_32, A_65))), inference(superposition, [status(thm), theory('equality')], [c_88, c_361])).
% 2.25/1.25  tff(c_413, plain, (![A_68, A_69]: (k9_relat_1(k6_relat_1(A_68), A_69)=A_69 | ~r1_tarski(A_69, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_403])).
% 2.25/1.25  tff(c_26, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.25/1.25  tff(c_440, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_413, c_26])).
% 2.25/1.25  tff(c_465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_440])).
% 2.25/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.25  
% 2.25/1.25  Inference rules
% 2.25/1.25  ----------------------
% 2.25/1.25  #Ref     : 0
% 2.25/1.25  #Sup     : 99
% 2.25/1.25  #Fact    : 0
% 2.25/1.25  #Define  : 0
% 2.25/1.25  #Split   : 1
% 2.25/1.25  #Chain   : 0
% 2.25/1.25  #Close   : 0
% 2.25/1.25  
% 2.25/1.25  Ordering : KBO
% 2.25/1.25  
% 2.25/1.25  Simplification rules
% 2.25/1.25  ----------------------
% 2.25/1.25  #Subsume      : 6
% 2.25/1.25  #Demod        : 21
% 2.25/1.25  #Tautology    : 54
% 2.25/1.25  #SimpNegUnit  : 0
% 2.25/1.25  #BackRed      : 0
% 2.25/1.25  
% 2.25/1.25  #Partial instantiations: 0
% 2.25/1.25  #Strategies tried      : 1
% 2.25/1.25  
% 2.25/1.25  Timing (in seconds)
% 2.25/1.25  ----------------------
% 2.25/1.26  Preprocessing        : 0.28
% 2.25/1.26  Parsing              : 0.16
% 2.25/1.26  CNF conversion       : 0.02
% 2.25/1.26  Main loop            : 0.23
% 2.25/1.26  Inferencing          : 0.10
% 2.25/1.26  Reduction            : 0.06
% 2.25/1.26  Demodulation         : 0.04
% 2.25/1.26  BG Simplification    : 0.01
% 2.25/1.26  Subsumption          : 0.04
% 2.25/1.26  Abstraction          : 0.01
% 2.25/1.26  MUC search           : 0.00
% 2.25/1.26  Cooper               : 0.00
% 2.25/1.26  Total                : 0.54
% 2.25/1.26  Index Insertion      : 0.00
% 2.25/1.26  Index Deletion       : 0.00
% 2.25/1.26  Index Matching       : 0.00
% 2.25/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
