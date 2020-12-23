%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:47 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   53 (  91 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 150 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_41,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_38,B_39] :
      ( k8_relat_1(A_38,B_39) = B_39
      | ~ r1_tarski(k2_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_40,B_41] :
      ( k8_relat_1(A_40,B_41) = B_41
      | ~ v5_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_59,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_56])).

tff(c_62,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_67,plain,(
    ! [B_42,A_43,C_44] :
      ( k8_relat_1(B_42,k8_relat_1(A_43,C_44)) = k8_relat_1(A_43,C_44)
      | ~ r1_tarski(A_43,B_42)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ! [B_42] :
      ( k8_relat_1(B_42,'#skF_4') = k8_relat_1('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_2',B_42)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_67])).

tff(c_87,plain,(
    ! [B_45] :
      ( k8_relat_1(B_45,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_62,c_82])).

tff(c_91,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_102,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k6_relset_1(A_47,B_48,C_49,D_50) = k8_relat_1(C_49,D_50)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [C_49] : k6_relset_1('#skF_1','#skF_2',C_49,'#skF_4') = k8_relat_1(C_49,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_106,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_107,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_106])).

tff(c_117,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( r2_relset_1(A_52,B_53,C_54,C_54)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_121,plain,(
    ! [C_56] :
      ( r2_relset_1('#skF_1','#skF_2',C_56,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_123,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_121])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:12:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.91/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.19  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 1.91/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.91/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.91/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.19  
% 1.91/1.20  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 1.91/1.20  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.91/1.20  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.91/1.20  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.91/1.20  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.91/1.20  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.91/1.20  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.91/1.20  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 1.91/1.20  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.91/1.20  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.20  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.20  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.20  tff(c_28, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.20  tff(c_31, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 1.91/1.20  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_31])).
% 1.91/1.20  tff(c_41, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.20  tff(c_45, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_41])).
% 1.91/1.20  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.20  tff(c_51, plain, (![A_38, B_39]: (k8_relat_1(A_38, B_39)=B_39 | ~r1_tarski(k2_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.20  tff(c_56, plain, (![A_40, B_41]: (k8_relat_1(A_40, B_41)=B_41 | ~v5_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_6, c_51])).
% 1.91/1.20  tff(c_59, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_56])).
% 1.91/1.20  tff(c_62, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59])).
% 1.91/1.20  tff(c_67, plain, (![B_42, A_43, C_44]: (k8_relat_1(B_42, k8_relat_1(A_43, C_44))=k8_relat_1(A_43, C_44) | ~r1_tarski(A_43, B_42) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.20  tff(c_82, plain, (![B_42]: (k8_relat_1(B_42, '#skF_4')=k8_relat_1('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', B_42) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_67])).
% 1.91/1.20  tff(c_87, plain, (![B_45]: (k8_relat_1(B_45, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_45))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_62, c_82])).
% 1.91/1.20  tff(c_91, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_87])).
% 1.91/1.20  tff(c_102, plain, (![A_47, B_48, C_49, D_50]: (k6_relset_1(A_47, B_48, C_49, D_50)=k8_relat_1(C_49, D_50) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.20  tff(c_105, plain, (![C_49]: (k6_relset_1('#skF_1', '#skF_2', C_49, '#skF_4')=k8_relat_1(C_49, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_102])).
% 1.91/1.20  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.20  tff(c_106, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_22])).
% 1.91/1.20  tff(c_107, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_106])).
% 1.91/1.20  tff(c_117, plain, (![A_52, B_53, C_54, D_55]: (r2_relset_1(A_52, B_53, C_54, C_54) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.20  tff(c_121, plain, (![C_56]: (r2_relset_1('#skF_1', '#skF_2', C_56, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_26, c_117])).
% 1.91/1.20  tff(c_123, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_121])).
% 1.91/1.20  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_123])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 22
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 0
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 0
% 1.91/1.20  #Demod        : 8
% 1.91/1.20  #Tautology    : 9
% 1.91/1.20  #SimpNegUnit  : 1
% 1.91/1.20  #BackRed      : 1
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.29
% 1.91/1.20  Parsing              : 0.16
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.13
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.02
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.45
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
