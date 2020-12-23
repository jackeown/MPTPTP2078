%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:22 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 154 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_58,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_412,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_416,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_412])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_457,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_461,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_457])).

tff(c_143,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_32,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_148,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_73])).

tff(c_34,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_171,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_relat_1(A_55),k1_relat_1(B_56))
      | ~ r1_tarski(A_55,B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_176,plain,(
    ! [A_9,B_56] :
      ( r1_tarski(A_9,k1_relat_1(B_56))
      | ~ r1_tarski(k6_relat_1(A_9),B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_171])).

tff(c_378,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,k1_relat_1(B_75))
      | ~ r1_tarski(k6_relat_1(A_74),B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_381,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_378])).

tff(c_388,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_381])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_388])).

tff(c_391,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_462,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_391])).

tff(c_20,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_481,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(k2_relat_1(A_97),k2_relat_1(B_98))
      | ~ r1_tarski(A_97,B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_489,plain,(
    ! [A_9,B_98] :
      ( r1_tarski(A_9,k2_relat_1(B_98))
      | ~ r1_tarski(k6_relat_1(A_9),B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_481])).

tff(c_580,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(A_112,k2_relat_1(B_113))
      | ~ r1_tarski(k6_relat_1(A_112),B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_489])).

tff(c_583,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_580])).

tff(c_590,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_583])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_595,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_590,c_2])).

tff(c_598,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_595])).

tff(c_604,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_598])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_416,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:54:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.42  
% 2.66/1.42  %Foreground sorts:
% 2.66/1.42  
% 2.66/1.42  
% 2.66/1.42  %Background operators:
% 2.66/1.42  
% 2.66/1.42  
% 2.66/1.42  %Foreground operators:
% 2.66/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.66/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.42  
% 2.66/1.44  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 2.66/1.44  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.66/1.44  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.66/1.44  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.66/1.44  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.66/1.44  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.66/1.44  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.66/1.44  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.66/1.44  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.66/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.66/1.44  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.44  tff(c_58, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.66/1.44  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.66/1.44  tff(c_412, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.66/1.44  tff(c_416, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_412])).
% 2.66/1.44  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.44  tff(c_457, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.44  tff(c_461, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_457])).
% 2.66/1.44  tff(c_143, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.66/1.44  tff(c_147, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.66/1.44  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.44  tff(c_73, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.66/1.44  tff(c_148, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_73])).
% 2.66/1.44  tff(c_34, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.44  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.44  tff(c_18, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.44  tff(c_171, plain, (![A_55, B_56]: (r1_tarski(k1_relat_1(A_55), k1_relat_1(B_56)) | ~r1_tarski(A_55, B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.66/1.44  tff(c_176, plain, (![A_9, B_56]: (r1_tarski(A_9, k1_relat_1(B_56)) | ~r1_tarski(k6_relat_1(A_9), B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_171])).
% 2.66/1.44  tff(c_378, plain, (![A_74, B_75]: (r1_tarski(A_74, k1_relat_1(B_75)) | ~r1_tarski(k6_relat_1(A_74), B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_176])).
% 2.66/1.44  tff(c_381, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_378])).
% 2.66/1.44  tff(c_388, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_381])).
% 2.66/1.44  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_388])).
% 2.66/1.44  tff(c_391, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.66/1.44  tff(c_462, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_461, c_391])).
% 2.66/1.44  tff(c_20, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.44  tff(c_481, plain, (![A_97, B_98]: (r1_tarski(k2_relat_1(A_97), k2_relat_1(B_98)) | ~r1_tarski(A_97, B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.66/1.44  tff(c_489, plain, (![A_9, B_98]: (r1_tarski(A_9, k2_relat_1(B_98)) | ~r1_tarski(k6_relat_1(A_9), B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_481])).
% 2.66/1.44  tff(c_580, plain, (![A_112, B_113]: (r1_tarski(A_112, k2_relat_1(B_113)) | ~r1_tarski(k6_relat_1(A_112), B_113) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_489])).
% 2.66/1.44  tff(c_583, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_580])).
% 2.66/1.44  tff(c_590, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_583])).
% 2.66/1.44  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.44  tff(c_595, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_590, c_2])).
% 2.66/1.44  tff(c_598, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_462, c_595])).
% 2.66/1.44  tff(c_604, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_598])).
% 2.66/1.44  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_416, c_604])).
% 2.66/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.44  
% 2.66/1.44  Inference rules
% 2.66/1.44  ----------------------
% 2.66/1.44  #Ref     : 0
% 2.66/1.44  #Sup     : 112
% 2.66/1.44  #Fact    : 0
% 2.66/1.44  #Define  : 0
% 2.66/1.44  #Split   : 6
% 2.66/1.44  #Chain   : 0
% 2.66/1.44  #Close   : 0
% 2.66/1.44  
% 2.66/1.44  Ordering : KBO
% 2.66/1.44  
% 2.66/1.44  Simplification rules
% 2.66/1.44  ----------------------
% 2.66/1.44  #Subsume      : 6
% 2.66/1.44  #Demod        : 87
% 2.66/1.44  #Tautology    : 44
% 2.66/1.44  #SimpNegUnit  : 2
% 2.66/1.44  #BackRed      : 6
% 2.66/1.44  
% 2.66/1.44  #Partial instantiations: 0
% 2.66/1.44  #Strategies tried      : 1
% 2.66/1.44  
% 2.66/1.44  Timing (in seconds)
% 2.66/1.44  ----------------------
% 2.66/1.44  Preprocessing        : 0.33
% 2.66/1.44  Parsing              : 0.18
% 2.66/1.44  CNF conversion       : 0.02
% 2.66/1.44  Main loop            : 0.30
% 2.66/1.44  Inferencing          : 0.12
% 2.66/1.44  Reduction            : 0.09
% 2.66/1.44  Demodulation         : 0.07
% 2.66/1.44  BG Simplification    : 0.01
% 2.66/1.44  Subsumption          : 0.05
% 2.66/1.44  Abstraction          : 0.02
% 2.66/1.44  MUC search           : 0.00
% 2.66/1.44  Cooper               : 0.00
% 2.66/1.44  Total                : 0.66
% 2.66/1.44  Index Insertion      : 0.00
% 2.66/1.44  Index Deletion       : 0.00
% 2.66/1.44  Index Matching       : 0.00
% 2.66/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
