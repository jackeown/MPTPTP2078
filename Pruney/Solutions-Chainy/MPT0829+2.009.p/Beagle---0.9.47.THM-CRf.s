%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:22 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 134 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 245 expanded)
%              Number of equality atoms :   24 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_34,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_371,plain,(
    ! [C_68,A_69,B_70,D_71] :
      ( r1_tarski(C_68,k1_relset_1(A_69,B_70,D_71))
      | ~ r1_tarski(k6_relat_1(C_68),D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_387,plain,(
    ! [A_73,B_74] :
      ( r1_tarski('#skF_2',k1_relset_1(A_73,B_74,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_36,c_371])).

tff(c_390,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_387])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_390])).

tff(c_395,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_64,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_68,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_507,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_relat_1(A_98),k2_relat_1(B_99))
      | ~ r1_tarski(A_98,B_99)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_518,plain,(
    ! [A_6,B_99] :
      ( r1_tarski(A_6,k2_relat_1(B_99))
      | ~ r1_tarski(k6_relat_1(A_6),B_99)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_507])).

tff(c_530,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,k2_relat_1(B_101))
      | ~ r1_tarski(k6_relat_1(A_100),B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_518])).

tff(c_533,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_530])).

tff(c_536,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_533])).

tff(c_465,plain,(
    ! [A_92,B_93] :
      ( k5_relat_1(k6_relat_1(A_92),B_93) = B_93
      | ~ r1_tarski(k1_relat_1(B_93),A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_468,plain,(
    ! [A_92,A_6] :
      ( k5_relat_1(k6_relat_1(A_92),k6_relat_1(A_6)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_92)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_465])).

tff(c_471,plain,(
    ! [A_94,A_95] :
      ( k5_relat_1(k6_relat_1(A_94),k6_relat_1(A_95)) = k6_relat_1(A_95)
      | ~ r1_tarski(A_95,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_468])).

tff(c_424,plain,(
    ! [B_86,A_87] :
      ( k5_relat_1(B_86,k6_relat_1(A_87)) = B_86
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_430,plain,(
    ! [A_6,A_87] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_87)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_87)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_424])).

tff(c_433,plain,(
    ! [A_6,A_87] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_87)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_430])).

tff(c_477,plain,(
    ! [A_95,A_94] :
      ( k6_relat_1(A_95) = k6_relat_1(A_94)
      | ~ r1_tarski(A_94,A_95)
      | ~ r1_tarski(A_95,A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_433])).

tff(c_539,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_536,c_477])).

tff(c_540,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_543,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_540])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_68,c_543])).

tff(c_548,plain,(
    k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_594,plain,(
    k1_relat_1(k6_relat_1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_10])).

tff(c_606,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_594])).

tff(c_643,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_646,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_643])).

tff(c_648,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_646])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.54  
% 2.29/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.54  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.54  
% 2.29/1.54  %Foreground sorts:
% 2.29/1.54  
% 2.29/1.54  
% 2.29/1.54  %Background operators:
% 2.29/1.54  
% 2.29/1.54  
% 2.29/1.54  %Foreground operators:
% 2.29/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.29/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.54  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.29/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.29/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.29/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.29/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.54  
% 2.58/1.55  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 2.58/1.55  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.58/1.55  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.58/1.55  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.55  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.55  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.58/1.55  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.58/1.55  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.58/1.55  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.58/1.55  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.58/1.55  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.58/1.55  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.55  tff(c_69, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.58/1.55  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.55  tff(c_36, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.55  tff(c_371, plain, (![C_68, A_69, B_70, D_71]: (r1_tarski(C_68, k1_relset_1(A_69, B_70, D_71)) | ~r1_tarski(k6_relat_1(C_68), D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.55  tff(c_387, plain, (![A_73, B_74]: (r1_tarski('#skF_2', k1_relset_1(A_73, B_74, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_36, c_371])).
% 2.58/1.55  tff(c_390, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_387])).
% 2.58/1.55  tff(c_394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_390])).
% 2.58/1.55  tff(c_395, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.58/1.55  tff(c_10, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.55  tff(c_59, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.58/1.55  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_59])).
% 2.58/1.55  tff(c_64, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.55  tff(c_68, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.58/1.55  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.55  tff(c_18, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.58/1.55  tff(c_12, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.55  tff(c_507, plain, (![A_98, B_99]: (r1_tarski(k2_relat_1(A_98), k2_relat_1(B_99)) | ~r1_tarski(A_98, B_99) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.55  tff(c_518, plain, (![A_6, B_99]: (r1_tarski(A_6, k2_relat_1(B_99)) | ~r1_tarski(k6_relat_1(A_6), B_99) | ~v1_relat_1(B_99) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_507])).
% 2.58/1.55  tff(c_530, plain, (![A_100, B_101]: (r1_tarski(A_100, k2_relat_1(B_101)) | ~r1_tarski(k6_relat_1(A_100), B_101) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_518])).
% 2.58/1.55  tff(c_533, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_530])).
% 2.58/1.55  tff(c_536, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_533])).
% 2.58/1.55  tff(c_465, plain, (![A_92, B_93]: (k5_relat_1(k6_relat_1(A_92), B_93)=B_93 | ~r1_tarski(k1_relat_1(B_93), A_92) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.55  tff(c_468, plain, (![A_92, A_6]: (k5_relat_1(k6_relat_1(A_92), k6_relat_1(A_6))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_92) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_465])).
% 2.58/1.55  tff(c_471, plain, (![A_94, A_95]: (k5_relat_1(k6_relat_1(A_94), k6_relat_1(A_95))=k6_relat_1(A_95) | ~r1_tarski(A_95, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_468])).
% 2.58/1.55  tff(c_424, plain, (![B_86, A_87]: (k5_relat_1(B_86, k6_relat_1(A_87))=B_86 | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.55  tff(c_430, plain, (![A_6, A_87]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_87))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_87) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_424])).
% 2.58/1.55  tff(c_433, plain, (![A_6, A_87]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_87))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_430])).
% 2.58/1.55  tff(c_477, plain, (![A_95, A_94]: (k6_relat_1(A_95)=k6_relat_1(A_94) | ~r1_tarski(A_94, A_95) | ~r1_tarski(A_95, A_94))), inference(superposition, [status(thm), theory('equality')], [c_471, c_433])).
% 2.58/1.55  tff(c_539, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_536, c_477])).
% 2.58/1.55  tff(c_540, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_539])).
% 2.58/1.55  tff(c_543, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_540])).
% 2.58/1.55  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_68, c_543])).
% 2.58/1.55  tff(c_548, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_539])).
% 2.58/1.55  tff(c_594, plain, (k1_relat_1(k6_relat_1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_548, c_10])).
% 2.58/1.55  tff(c_606, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_594])).
% 2.58/1.55  tff(c_643, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.58/1.55  tff(c_646, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_643])).
% 2.58/1.55  tff(c_648, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_606, c_646])).
% 2.58/1.55  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_395, c_648])).
% 2.58/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.55  
% 2.58/1.55  Inference rules
% 2.58/1.55  ----------------------
% 2.58/1.55  #Ref     : 0
% 2.58/1.55  #Sup     : 134
% 2.58/1.55  #Fact    : 0
% 2.58/1.55  #Define  : 0
% 2.58/1.55  #Split   : 5
% 2.58/1.55  #Chain   : 0
% 2.58/1.55  #Close   : 0
% 2.58/1.55  
% 2.58/1.55  Ordering : KBO
% 2.58/1.55  
% 2.58/1.55  Simplification rules
% 2.58/1.55  ----------------------
% 2.58/1.55  #Subsume      : 3
% 2.58/1.55  #Demod        : 77
% 2.58/1.55  #Tautology    : 54
% 2.58/1.55  #SimpNegUnit  : 2
% 2.58/1.55  #BackRed      : 5
% 2.58/1.55  
% 2.58/1.55  #Partial instantiations: 0
% 2.58/1.55  #Strategies tried      : 1
% 2.58/1.55  
% 2.58/1.55  Timing (in seconds)
% 2.58/1.55  ----------------------
% 2.58/1.56  Preprocessing        : 0.32
% 2.58/1.56  Parsing              : 0.16
% 2.58/1.56  CNF conversion       : 0.02
% 2.58/1.56  Main loop            : 0.29
% 2.58/1.56  Inferencing          : 0.11
% 2.58/1.56  Reduction            : 0.09
% 2.58/1.56  Demodulation         : 0.06
% 2.58/1.56  BG Simplification    : 0.02
% 2.58/1.56  Subsumption          : 0.05
% 2.58/1.56  Abstraction          : 0.02
% 2.58/1.56  MUC search           : 0.00
% 2.58/1.56  Cooper               : 0.00
% 2.58/1.56  Total                : 0.64
% 2.58/1.56  Index Insertion      : 0.00
% 2.58/1.56  Index Deletion       : 0.00
% 2.58/1.56  Index Matching       : 0.00
% 2.58/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
