%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:25 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 122 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 230 expanded)
%              Number of equality atoms :   17 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_503,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_512,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_503])).

tff(c_158,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_167,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_158])).

tff(c_30,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_168,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_66])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_32,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(A_38)
      | ~ v1_relat_1(B_39)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_111,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_121,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_111])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_relat_1(A_36),k1_relat_1(B_37))
      | ~ r1_tarski(A_36,B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_439,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,k1_relat_1(B_84))
      | ~ r1_tarski(k6_relat_1(A_83),B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(k6_relat_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_92])).

tff(c_442,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_439])).

tff(c_449,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_91,c_442])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_449])).

tff(c_452,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_513,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_452])).

tff(c_613,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k2_relset_1(A_111,B_112,C_113),k1_zfmisc_1(B_112))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_633,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_613])).

tff(c_639,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_633])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_647,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_639,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_652,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_647,c_2])).

tff(c_656,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_652])).

tff(c_471,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_477,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_471])).

tff(c_481,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_477])).

tff(c_482,plain,(
    ! [A_89,B_90] :
      ( v1_relat_1(A_89)
      | ~ v1_relat_1(B_90)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_10,c_471])).

tff(c_491,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_482])).

tff(c_501,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_491])).

tff(c_22,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_599,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(k2_relat_1(A_109),k2_relat_1(B_110))
      | ~ r1_tarski(A_109,B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_799,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(A_136,k2_relat_1(B_137))
      | ~ r1_tarski(k6_relat_1(A_136),B_137)
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(k6_relat_1(A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_599])).

tff(c_802,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_799])).

tff(c_809,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_481,c_802])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_656,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:01:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.32  
% 2.77/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.33  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.77/1.33  
% 2.77/1.33  %Foreground sorts:
% 2.77/1.33  
% 2.77/1.33  
% 2.77/1.33  %Background operators:
% 2.77/1.33  
% 2.77/1.33  
% 2.77/1.33  %Foreground operators:
% 2.77/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.33  
% 2.77/1.34  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 2.77/1.34  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.77/1.34  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.77/1.34  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.34  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.34  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.34  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.77/1.34  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.77/1.34  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.77/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.34  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.34  tff(c_503, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.77/1.34  tff(c_512, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_503])).
% 2.77/1.34  tff(c_158, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.77/1.34  tff(c_167, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_158])).
% 2.77/1.34  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.34  tff(c_66, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.77/1.34  tff(c_168, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_66])).
% 2.77/1.34  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.34  tff(c_81, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.34  tff(c_87, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.77/1.34  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_87])).
% 2.77/1.34  tff(c_32, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.34  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.34  tff(c_102, plain, (![A_38, B_39]: (v1_relat_1(A_38) | ~v1_relat_1(B_39) | ~r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_10, c_81])).
% 2.77/1.34  tff(c_111, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_102])).
% 2.77/1.34  tff(c_121, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_111])).
% 2.77/1.34  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.34  tff(c_92, plain, (![A_36, B_37]: (r1_tarski(k1_relat_1(A_36), k1_relat_1(B_37)) | ~r1_tarski(A_36, B_37) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.34  tff(c_439, plain, (![A_83, B_84]: (r1_tarski(A_83, k1_relat_1(B_84)) | ~r1_tarski(k6_relat_1(A_83), B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(k6_relat_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_92])).
% 2.77/1.34  tff(c_442, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_439])).
% 2.77/1.34  tff(c_449, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_91, c_442])).
% 2.77/1.34  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_449])).
% 2.77/1.34  tff(c_452, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.77/1.34  tff(c_513, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_512, c_452])).
% 2.77/1.34  tff(c_613, plain, (![A_111, B_112, C_113]: (m1_subset_1(k2_relset_1(A_111, B_112, C_113), k1_zfmisc_1(B_112)) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.34  tff(c_633, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_512, c_613])).
% 2.77/1.34  tff(c_639, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_633])).
% 2.77/1.34  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.34  tff(c_647, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_639, c_8])).
% 2.77/1.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.34  tff(c_652, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_647, c_2])).
% 2.77/1.34  tff(c_656, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_513, c_652])).
% 2.77/1.34  tff(c_471, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.34  tff(c_477, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_471])).
% 2.77/1.34  tff(c_481, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_477])).
% 2.77/1.34  tff(c_482, plain, (![A_89, B_90]: (v1_relat_1(A_89) | ~v1_relat_1(B_90) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_10, c_471])).
% 2.77/1.34  tff(c_491, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_482])).
% 2.77/1.34  tff(c_501, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_491])).
% 2.77/1.34  tff(c_22, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.34  tff(c_599, plain, (![A_109, B_110]: (r1_tarski(k2_relat_1(A_109), k2_relat_1(B_110)) | ~r1_tarski(A_109, B_110) | ~v1_relat_1(B_110) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.34  tff(c_799, plain, (![A_136, B_137]: (r1_tarski(A_136, k2_relat_1(B_137)) | ~r1_tarski(k6_relat_1(A_136), B_137) | ~v1_relat_1(B_137) | ~v1_relat_1(k6_relat_1(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_599])).
% 2.77/1.34  tff(c_802, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_799])).
% 2.77/1.34  tff(c_809, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_481, c_802])).
% 2.77/1.34  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_656, c_809])).
% 2.77/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.34  
% 2.77/1.34  Inference rules
% 2.77/1.34  ----------------------
% 2.77/1.34  #Ref     : 0
% 2.77/1.34  #Sup     : 165
% 2.77/1.34  #Fact    : 0
% 2.77/1.34  #Define  : 0
% 2.77/1.34  #Split   : 10
% 2.77/1.34  #Chain   : 0
% 2.77/1.34  #Close   : 0
% 2.77/1.34  
% 2.77/1.34  Ordering : KBO
% 2.77/1.34  
% 2.77/1.34  Simplification rules
% 2.77/1.34  ----------------------
% 2.77/1.34  #Subsume      : 12
% 2.77/1.34  #Demod        : 70
% 2.77/1.34  #Tautology    : 48
% 2.77/1.34  #SimpNegUnit  : 6
% 2.77/1.34  #BackRed      : 7
% 2.77/1.34  
% 2.77/1.34  #Partial instantiations: 0
% 2.77/1.34  #Strategies tried      : 1
% 2.77/1.34  
% 2.77/1.34  Timing (in seconds)
% 2.77/1.34  ----------------------
% 2.77/1.34  Preprocessing        : 0.31
% 2.77/1.34  Parsing              : 0.17
% 2.77/1.34  CNF conversion       : 0.02
% 2.77/1.34  Main loop            : 0.35
% 2.77/1.35  Inferencing          : 0.13
% 2.77/1.35  Reduction            : 0.10
% 2.77/1.35  Demodulation         : 0.07
% 2.77/1.35  BG Simplification    : 0.02
% 2.77/1.35  Subsumption          : 0.06
% 2.77/1.35  Abstraction          : 0.02
% 2.77/1.35  MUC search           : 0.00
% 2.77/1.35  Cooper               : 0.00
% 2.77/1.35  Total                : 0.69
% 2.77/1.35  Index Insertion      : 0.00
% 2.77/1.35  Index Deletion       : 0.00
% 2.77/1.35  Index Matching       : 0.00
% 2.77/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
