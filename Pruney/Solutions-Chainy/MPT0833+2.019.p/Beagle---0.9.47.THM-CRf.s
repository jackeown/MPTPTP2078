%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:47 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 131 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_45,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_71,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k2_relat_1(B_39),A_40)
      | ~ v5_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [B_51,A_52] :
      ( k2_xboole_0(k2_relat_1(B_51),A_52) = A_52
      | ~ v5_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [B_53,C_54,A_55] :
      ( r1_tarski(k2_relat_1(B_53),C_54)
      | ~ r1_tarski(A_55,C_54)
      | ~ v5_relat_1(B_53,A_55)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_114,plain,(
    ! [B_56] :
      ( r1_tarski(k2_relat_1(B_56),'#skF_3')
      | ~ v5_relat_1(B_56,'#skF_2')
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_26,c_104])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( v5_relat_1(B_10,A_9)
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [B_57] :
      ( v5_relat_1(B_57,'#skF_3')
      | ~ v5_relat_1(B_57,'#skF_2')
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_114,c_8])).

tff(c_133,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_130])).

tff(c_136,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_133])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [A_47,B_48] :
      ( k8_relat_1(A_47,B_48) = B_48
      | ~ r1_tarski(k2_relat_1(B_48),A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    ! [A_9,B_10] :
      ( k8_relat_1(A_9,B_10) = B_10
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_139,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_80])).

tff(c_142,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_139])).

tff(c_143,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k6_relset_1(A_58,B_59,C_60,D_61) = k8_relat_1(C_60,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    ! [C_60] : k6_relset_1('#skF_1','#skF_2',C_60,'#skF_4') = k8_relat_1(C_60,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_143])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_151,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_24])).

tff(c_152,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_151])).

tff(c_240,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( r2_relset_1(A_71,B_72,C_73,C_73)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_244,plain,(
    ! [C_75] :
      ( r2_relset_1('#skF_1','#skF_2',C_75,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_240])).

tff(c_246,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_244])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n004.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:50:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.22  
% 2.06/1.22  %Foreground sorts:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Background operators:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Foreground operators:
% 2.06/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.06/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.22  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.06/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.06/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.06/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.22  
% 2.14/1.23  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.14/1.23  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.14/1.23  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.14/1.23  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.23  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.14/1.23  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.14/1.23  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.14/1.23  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.14/1.23  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.14/1.23  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.14/1.23  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.23  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.23  tff(c_39, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.23  tff(c_42, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.14/1.23  tff(c_45, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 2.14/1.23  tff(c_71, plain, (![C_44, B_45, A_46]: (v5_relat_1(C_44, B_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.23  tff(c_75, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_71])).
% 2.14/1.23  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.23  tff(c_57, plain, (![B_39, A_40]: (r1_tarski(k2_relat_1(B_39), A_40) | ~v5_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.23  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.23  tff(c_92, plain, (![B_51, A_52]: (k2_xboole_0(k2_relat_1(B_51), A_52)=A_52 | ~v5_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_57, c_4])).
% 2.14/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.23  tff(c_104, plain, (![B_53, C_54, A_55]: (r1_tarski(k2_relat_1(B_53), C_54) | ~r1_tarski(A_55, C_54) | ~v5_relat_1(B_53, A_55) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 2.14/1.23  tff(c_114, plain, (![B_56]: (r1_tarski(k2_relat_1(B_56), '#skF_3') | ~v5_relat_1(B_56, '#skF_2') | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_26, c_104])).
% 2.14/1.23  tff(c_8, plain, (![B_10, A_9]: (v5_relat_1(B_10, A_9) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.23  tff(c_130, plain, (![B_57]: (v5_relat_1(B_57, '#skF_3') | ~v5_relat_1(B_57, '#skF_2') | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_114, c_8])).
% 2.14/1.23  tff(c_133, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_75, c_130])).
% 2.14/1.23  tff(c_136, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_133])).
% 2.14/1.23  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.23  tff(c_76, plain, (![A_47, B_48]: (k8_relat_1(A_47, B_48)=B_48 | ~r1_tarski(k2_relat_1(B_48), A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.23  tff(c_80, plain, (![A_9, B_10]: (k8_relat_1(A_9, B_10)=B_10 | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_10, c_76])).
% 2.14/1.23  tff(c_139, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_80])).
% 2.14/1.23  tff(c_142, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_139])).
% 2.14/1.23  tff(c_143, plain, (![A_58, B_59, C_60, D_61]: (k6_relset_1(A_58, B_59, C_60, D_61)=k8_relat_1(C_60, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.23  tff(c_146, plain, (![C_60]: (k6_relset_1('#skF_1', '#skF_2', C_60, '#skF_4')=k8_relat_1(C_60, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_143])).
% 2.14/1.23  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.23  tff(c_151, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_24])).
% 2.14/1.23  tff(c_152, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_151])).
% 2.14/1.23  tff(c_240, plain, (![A_71, B_72, C_73, D_74]: (r2_relset_1(A_71, B_72, C_73, C_73) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.23  tff(c_244, plain, (![C_75]: (r2_relset_1('#skF_1', '#skF_2', C_75, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_28, c_240])).
% 2.14/1.23  tff(c_246, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_244])).
% 2.14/1.23  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_246])).
% 2.14/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  Inference rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Ref     : 0
% 2.14/1.23  #Sup     : 48
% 2.14/1.23  #Fact    : 0
% 2.14/1.23  #Define  : 0
% 2.14/1.23  #Split   : 0
% 2.14/1.23  #Chain   : 0
% 2.14/1.23  #Close   : 0
% 2.14/1.23  
% 2.14/1.23  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 1
% 2.14/1.24  #Demod        : 15
% 2.14/1.24  #Tautology    : 18
% 2.14/1.24  #SimpNegUnit  : 1
% 2.14/1.24  #BackRed      : 1
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.24  Preprocessing        : 0.29
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.19
% 2.14/1.24  Inferencing          : 0.08
% 2.14/1.24  Reduction            : 0.05
% 2.14/1.24  Demodulation         : 0.04
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.03
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.51
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
