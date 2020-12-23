%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:21 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 144 expanded)
%              Number of leaves         :   31 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 269 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_494,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_503,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_494])).

tff(c_147,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_147])).

tff(c_30,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_60,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_157,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_60])).

tff(c_32,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_318,plain,(
    ! [C_83,A_84,B_85,D_86] :
      ( r1_tarski(C_83,k1_relset_1(A_84,B_85,D_86))
      | ~ r1_tarski(k6_relat_1(C_83),D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_363,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_2',k1_relset_1(A_87,B_88,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(resolution,[status(thm)],[c_32,c_318])).

tff(c_369,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_363])).

tff(c_372,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_369])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_372])).

tff(c_375,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_504,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_375])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_377,plain,(
    ! [A_89,B_90] :
      ( v1_relat_1(A_89)
      | ~ v1_relat_1(B_90)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_389,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_377])).

tff(c_390,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_391,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_398,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_391])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_398])).

tff(c_405,plain,(
    v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_404,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_532,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1(k2_relset_1(A_122,B_123,C_124),k1_zfmisc_1(B_123))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_556,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_532])).

tff(c_564,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_556])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k9_relat_1(k6_relat_1(A_15),B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_574,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_564,c_16])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( k9_relat_1(B_14,k2_relat_1(A_12)) = k2_relat_1(k5_relat_1(A_12,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_585,plain,
    ( k2_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))) = k2_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_14])).

tff(c_598,plain,(
    k2_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_404,c_585])).

tff(c_622,plain,
    ( k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_598])).

tff(c_626,plain,(
    k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_622])).

tff(c_720,plain,(
    ! [C_144,A_145,B_146,D_147] :
      ( r1_tarski(C_144,k2_relset_1(A_145,B_146,D_147))
      | ~ r1_tarski(k6_relat_1(C_144),D_147)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_724,plain,(
    ! [A_148,B_149] :
      ( r1_tarski('#skF_2',k2_relset_1(A_148,B_149,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(resolution,[status(thm)],[c_32,c_720])).

tff(c_730,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_724])).

tff(c_733,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_730])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_relat_1(k8_relat_1(A_8,B_9)) = A_8
      | ~ r1_tarski(A_8,k2_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_736,plain,
    ( k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_733,c_10])).

tff(c_742,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_626,c_736])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.37  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.37  
% 2.74/1.37  %Foreground sorts:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Background operators:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Foreground operators:
% 2.74/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.74/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.37  
% 2.74/1.38  tff(f_94, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 2.74/1.38  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.74/1.38  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.74/1.38  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.74/1.38  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.38  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.74/1.38  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.38  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.74/1.38  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.74/1.38  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.74/1.38  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.74/1.38  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 2.74/1.38  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.74/1.38  tff(c_494, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.74/1.38  tff(c_503, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_494])).
% 2.74/1.38  tff(c_147, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.74/1.38  tff(c_156, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_147])).
% 2.74/1.38  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.74/1.38  tff(c_60, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.74/1.38  tff(c_157, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_60])).
% 2.74/1.38  tff(c_32, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.74/1.38  tff(c_318, plain, (![C_83, A_84, B_85, D_86]: (r1_tarski(C_83, k1_relset_1(A_84, B_85, D_86)) | ~r1_tarski(k6_relat_1(C_83), D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.38  tff(c_363, plain, (![A_87, B_88]: (r1_tarski('#skF_2', k1_relset_1(A_87, B_88, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(resolution, [status(thm)], [c_32, c_318])).
% 2.74/1.38  tff(c_369, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_363])).
% 2.74/1.38  tff(c_372, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_369])).
% 2.74/1.38  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_372])).
% 2.74/1.38  tff(c_375, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.74/1.38  tff(c_504, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_375])).
% 2.74/1.38  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.38  tff(c_50, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.38  tff(c_377, plain, (![A_89, B_90]: (v1_relat_1(A_89) | ~v1_relat_1(B_90) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.74/1.38  tff(c_389, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_377])).
% 2.74/1.38  tff(c_390, plain, (~v1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_389])).
% 2.74/1.38  tff(c_391, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.38  tff(c_398, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_391])).
% 2.74/1.38  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_398])).
% 2.74/1.38  tff(c_405, plain, (v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_389])).
% 2.74/1.38  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.38  tff(c_404, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_389])).
% 2.74/1.38  tff(c_532, plain, (![A_122, B_123, C_124]: (m1_subset_1(k2_relset_1(A_122, B_123, C_124), k1_zfmisc_1(B_123)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.74/1.38  tff(c_556, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_503, c_532])).
% 2.74/1.38  tff(c_564, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_556])).
% 2.74/1.38  tff(c_16, plain, (![A_15, B_16]: (k9_relat_1(k6_relat_1(A_15), B_16)=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.38  tff(c_574, plain, (k9_relat_1(k6_relat_1('#skF_2'), k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_564, c_16])).
% 2.74/1.38  tff(c_14, plain, (![B_14, A_12]: (k9_relat_1(B_14, k2_relat_1(A_12))=k2_relat_1(k5_relat_1(A_12, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.74/1.38  tff(c_585, plain, (k2_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))=k2_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_574, c_14])).
% 2.74/1.38  tff(c_598, plain, (k2_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_404, c_585])).
% 2.74/1.38  tff(c_622, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_598])).
% 2.74/1.38  tff(c_626, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_622])).
% 2.74/1.38  tff(c_720, plain, (![C_144, A_145, B_146, D_147]: (r1_tarski(C_144, k2_relset_1(A_145, B_146, D_147)) | ~r1_tarski(k6_relat_1(C_144), D_147) | ~m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.38  tff(c_724, plain, (![A_148, B_149]: (r1_tarski('#skF_2', k2_relset_1(A_148, B_149, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(resolution, [status(thm)], [c_32, c_720])).
% 2.74/1.38  tff(c_730, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_724])).
% 2.74/1.38  tff(c_733, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_730])).
% 2.74/1.38  tff(c_10, plain, (![A_8, B_9]: (k2_relat_1(k8_relat_1(A_8, B_9))=A_8 | ~r1_tarski(A_8, k2_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.74/1.38  tff(c_736, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_733, c_10])).
% 2.74/1.38  tff(c_742, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_405, c_626, c_736])).
% 2.74/1.38  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_504, c_742])).
% 2.74/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  Inference rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Ref     : 1
% 2.74/1.38  #Sup     : 155
% 2.74/1.38  #Fact    : 0
% 2.74/1.38  #Define  : 0
% 2.74/1.38  #Split   : 7
% 2.74/1.38  #Chain   : 0
% 2.74/1.38  #Close   : 0
% 2.74/1.38  
% 2.74/1.38  Ordering : KBO
% 2.74/1.38  
% 2.74/1.39  Simplification rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Subsume      : 9
% 2.74/1.39  #Demod        : 60
% 2.74/1.39  #Tautology    : 61
% 2.74/1.39  #SimpNegUnit  : 8
% 2.74/1.39  #BackRed      : 11
% 2.74/1.39  
% 2.74/1.39  #Partial instantiations: 0
% 2.74/1.39  #Strategies tried      : 1
% 2.74/1.39  
% 2.74/1.39  Timing (in seconds)
% 2.74/1.39  ----------------------
% 2.74/1.39  Preprocessing        : 0.31
% 2.74/1.39  Parsing              : 0.17
% 2.74/1.39  CNF conversion       : 0.02
% 2.74/1.39  Main loop            : 0.32
% 2.74/1.39  Inferencing          : 0.13
% 2.74/1.39  Reduction            : 0.09
% 2.74/1.39  Demodulation         : 0.06
% 2.74/1.39  BG Simplification    : 0.02
% 2.74/1.39  Subsumption          : 0.06
% 2.74/1.39  Abstraction          : 0.02
% 2.74/1.39  MUC search           : 0.00
% 2.74/1.39  Cooper               : 0.00
% 2.74/1.39  Total                : 0.67
% 2.74/1.39  Index Insertion      : 0.00
% 2.74/1.39  Index Deletion       : 0.00
% 2.74/1.39  Index Matching       : 0.00
% 2.74/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
