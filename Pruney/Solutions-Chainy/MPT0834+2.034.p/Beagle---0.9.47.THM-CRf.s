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
% DateTime   : Thu Dec  3 10:07:54 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 114 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  108 ( 173 expanded)
%              Number of equality atoms :   43 (  65 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_59,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_65,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_67,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_71,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_392,plain,(
    ! [B_105,A_106] :
      ( k5_relat_1(B_105,k6_relat_1(A_106)) = B_105
      | ~ r1_tarski(k2_relat_1(B_105),A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_402,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_392])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_460,plain,(
    ! [A_117,B_118] :
      ( k10_relat_1(A_117,k1_relat_1(B_118)) = k1_relat_1(k5_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_469,plain,(
    ! [A_117,A_16] :
      ( k1_relat_1(k5_relat_1(A_117,k6_relat_1(A_16))) = k10_relat_1(A_117,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_460])).

tff(c_474,plain,(
    ! [A_119,A_120] :
      ( k1_relat_1(k5_relat_1(A_119,k6_relat_1(A_120))) = k10_relat_1(A_119,A_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_469])).

tff(c_515,plain,(
    ! [B_123,A_124] :
      ( k10_relat_1(B_123,A_124) = k1_relat_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v5_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_474])).

tff(c_521,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_515])).

tff(c_527,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_521])).

tff(c_588,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k8_relset_1(A_132,B_133,C_134,D_135) = k10_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_591,plain,(
    ! [D_135] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_135) = k10_relat_1('#skF_3',D_135) ),
    inference(resolution,[status(thm)],[c_38,c_588])).

tff(c_436,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_440,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_436])).

tff(c_110,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_114,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_110])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_16])).

tff(c_120,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_117])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_12])).

tff(c_128,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_124])).

tff(c_317,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_320,plain,(
    ! [D_91] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_91) = k9_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_38,c_317])).

tff(c_183,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_187,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_36,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_192,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_72])).

tff(c_321,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_192])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_321])).

tff(c_325,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_441,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_325])).

tff(c_592,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_441])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:01:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.39  
% 2.43/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.40  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.40  
% 2.43/1.40  %Foreground sorts:
% 2.43/1.40  
% 2.43/1.40  
% 2.43/1.40  %Background operators:
% 2.43/1.40  
% 2.43/1.40  
% 2.43/1.40  %Foreground operators:
% 2.43/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.43/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.43/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.43/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.43/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.43/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.43/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.43/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.43/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.43/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.43/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.43/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.40  
% 2.43/1.41  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.43/1.41  tff(f_98, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.43/1.41  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.43/1.41  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.43/1.41  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.43/1.41  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.43/1.41  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.43/1.41  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.43/1.41  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.43/1.41  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.43/1.41  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.43/1.41  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.43/1.41  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.43/1.41  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.43/1.41  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.43/1.41  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.43/1.41  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.43/1.41  tff(c_59, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.43/1.41  tff(c_62, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_59])).
% 2.43/1.41  tff(c_65, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_62])).
% 2.43/1.41  tff(c_67, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.41  tff(c_71, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_67])).
% 2.43/1.41  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.41  tff(c_392, plain, (![B_105, A_106]: (k5_relat_1(B_105, k6_relat_1(A_106))=B_105 | ~r1_tarski(k2_relat_1(B_105), A_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.43/1.41  tff(c_402, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_392])).
% 2.43/1.41  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.41  tff(c_18, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.41  tff(c_460, plain, (![A_117, B_118]: (k10_relat_1(A_117, k1_relat_1(B_118))=k1_relat_1(k5_relat_1(A_117, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.41  tff(c_469, plain, (![A_117, A_16]: (k1_relat_1(k5_relat_1(A_117, k6_relat_1(A_16)))=k10_relat_1(A_117, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_18, c_460])).
% 2.43/1.41  tff(c_474, plain, (![A_119, A_120]: (k1_relat_1(k5_relat_1(A_119, k6_relat_1(A_120)))=k10_relat_1(A_119, A_120) | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_469])).
% 2.43/1.41  tff(c_515, plain, (![B_123, A_124]: (k10_relat_1(B_123, A_124)=k1_relat_1(B_123) | ~v1_relat_1(B_123) | ~v5_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_402, c_474])).
% 2.43/1.41  tff(c_521, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_515])).
% 2.43/1.41  tff(c_527, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_521])).
% 2.43/1.41  tff(c_588, plain, (![A_132, B_133, C_134, D_135]: (k8_relset_1(A_132, B_133, C_134, D_135)=k10_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.41  tff(c_591, plain, (![D_135]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_135)=k10_relat_1('#skF_3', D_135))), inference(resolution, [status(thm)], [c_38, c_588])).
% 2.43/1.41  tff(c_436, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.41  tff(c_440, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_436])).
% 2.43/1.41  tff(c_110, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.41  tff(c_114, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_110])).
% 2.43/1.41  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.43/1.41  tff(c_117, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_16])).
% 2.43/1.41  tff(c_120, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_117])).
% 2.43/1.41  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.41  tff(c_124, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_120, c_12])).
% 2.43/1.41  tff(c_128, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_124])).
% 2.43/1.41  tff(c_317, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.41  tff(c_320, plain, (![D_91]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_91)=k9_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_38, c_317])).
% 2.43/1.41  tff(c_183, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.43/1.41  tff(c_187, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_183])).
% 2.43/1.41  tff(c_36, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.43/1.41  tff(c_72, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.43/1.41  tff(c_192, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_72])).
% 2.43/1.41  tff(c_321, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_192])).
% 2.43/1.41  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_321])).
% 2.43/1.41  tff(c_325, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.43/1.41  tff(c_441, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_325])).
% 2.43/1.41  tff(c_592, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_441])).
% 2.43/1.41  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_527, c_592])).
% 2.43/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.41  
% 2.43/1.41  Inference rules
% 2.43/1.41  ----------------------
% 2.43/1.41  #Ref     : 0
% 2.43/1.41  #Sup     : 126
% 2.43/1.41  #Fact    : 0
% 2.43/1.41  #Define  : 0
% 2.43/1.41  #Split   : 1
% 2.43/1.41  #Chain   : 0
% 2.43/1.41  #Close   : 0
% 2.43/1.41  
% 2.43/1.41  Ordering : KBO
% 2.43/1.41  
% 2.43/1.41  Simplification rules
% 2.43/1.41  ----------------------
% 2.43/1.41  #Subsume      : 7
% 2.43/1.41  #Demod        : 66
% 2.43/1.41  #Tautology    : 74
% 2.43/1.41  #SimpNegUnit  : 0
% 2.43/1.41  #BackRed      : 5
% 2.43/1.41  
% 2.43/1.41  #Partial instantiations: 0
% 2.43/1.41  #Strategies tried      : 1
% 2.43/1.41  
% 2.43/1.41  Timing (in seconds)
% 2.43/1.41  ----------------------
% 2.43/1.41  Preprocessing        : 0.32
% 2.43/1.41  Parsing              : 0.18
% 2.43/1.41  CNF conversion       : 0.02
% 2.43/1.41  Main loop            : 0.27
% 2.43/1.41  Inferencing          : 0.11
% 2.43/1.41  Reduction            : 0.08
% 2.43/1.41  Demodulation         : 0.06
% 2.43/1.41  BG Simplification    : 0.02
% 2.43/1.41  Subsumption          : 0.03
% 2.43/1.41  Abstraction          : 0.01
% 2.43/1.41  MUC search           : 0.00
% 2.43/1.41  Cooper               : 0.00
% 2.43/1.42  Total                : 0.62
% 2.43/1.42  Index Insertion      : 0.00
% 2.43/1.42  Index Deletion       : 0.00
% 2.43/1.42  Index Matching       : 0.00
% 2.43/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
