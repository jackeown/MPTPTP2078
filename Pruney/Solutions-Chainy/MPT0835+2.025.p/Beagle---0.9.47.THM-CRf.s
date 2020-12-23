%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 127 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 183 expanded)
%              Number of equality atoms :   52 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_12,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_456,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_466,plain,(
    ! [D_119] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_119) = k9_relat_1('#skF_3',D_119) ),
    inference(resolution,[status(thm)],[c_32,c_456])).

tff(c_373,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_386,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_373])).

tff(c_625,plain,(
    ! [A_150,B_151,C_152] :
      ( k7_relset_1(A_150,B_151,C_152,A_150) = k2_relset_1(A_150,B_151,C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_630,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_625])).

tff(c_636,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_386,c_630])).

tff(c_520,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k8_relset_1(A_131,B_132,C_133,D_134) = k10_relat_1(C_133,D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_530,plain,(
    ! [D_134] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_134) = k10_relat_1('#skF_3',D_134) ),
    inference(resolution,[status(thm)],[c_32,c_520])).

tff(c_427,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_440,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_427])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_44,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_33,c_44])).

tff(c_109,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,A_49) = B_48
      | ~ r1_tarski(k1_relat_1(B_48),A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [B_53] :
      ( k7_relat_1(B_53,k1_relat_1(B_53)) = B_53
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [B_53] :
      ( k9_relat_1(B_53,k1_relat_1(B_53)) = k2_relat_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_10])).

tff(c_239,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k8_relset_1(A_73,B_74,C_75,D_76) = k10_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_249,plain,(
    ! [D_76] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_76) = k10_relat_1('#skF_3',D_76) ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_177,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_190,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_289,plain,(
    ! [A_88,B_89,C_90] :
      ( k8_relset_1(A_88,B_89,C_90,B_89) = k1_relset_1(A_88,B_89,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_294,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_289])).

tff(c_300,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_190,c_294])).

tff(c_205,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k7_relset_1(A_65,B_66,C_67,D_68) = k9_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_215,plain,(
    ! [D_68] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_68) = k9_relat_1('#skF_3',D_68) ),
    inference(resolution,[status(thm)],[c_32,c_205])).

tff(c_115,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_30,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_155,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_74])).

tff(c_217,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_155])).

tff(c_251,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_217])).

tff(c_303,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_251])).

tff(c_310,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_303])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_310])).

tff(c_315,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_442,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_315])).

tff(c_488,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_442])).

tff(c_532,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_488])).

tff(c_639,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_532])).

tff(c_646,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_639])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.40  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.40  
% 2.62/1.40  %Foreground sorts:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Background operators:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Foreground operators:
% 2.62/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.62/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.62/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.40  
% 2.62/1.42  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.62/1.42  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.42  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.62/1.42  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.62/1.42  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.42  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.62/1.42  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.62/1.42  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.42  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.62/1.42  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.62/1.42  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.62/1.42  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.62/1.42  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.62/1.42  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.42  tff(c_59, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.42  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_59])).
% 2.62/1.42  tff(c_12, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.42  tff(c_456, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.42  tff(c_466, plain, (![D_119]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_119)=k9_relat_1('#skF_3', D_119))), inference(resolution, [status(thm)], [c_32, c_456])).
% 2.62/1.42  tff(c_373, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.42  tff(c_386, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_373])).
% 2.62/1.42  tff(c_625, plain, (![A_150, B_151, C_152]: (k7_relset_1(A_150, B_151, C_152, A_150)=k2_relset_1(A_150, B_151, C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.42  tff(c_630, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_625])).
% 2.62/1.42  tff(c_636, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_386, c_630])).
% 2.62/1.42  tff(c_520, plain, (![A_131, B_132, C_133, D_134]: (k8_relset_1(A_131, B_132, C_133, D_134)=k10_relat_1(C_133, D_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.42  tff(c_530, plain, (![D_134]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_134)=k10_relat_1('#skF_3', D_134))), inference(resolution, [status(thm)], [c_32, c_520])).
% 2.62/1.42  tff(c_427, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.42  tff(c_440, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_427])).
% 2.62/1.42  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.42  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.42  tff(c_33, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.62/1.42  tff(c_44, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.42  tff(c_52, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_33, c_44])).
% 2.62/1.42  tff(c_109, plain, (![B_48, A_49]: (k7_relat_1(B_48, A_49)=B_48 | ~r1_tarski(k1_relat_1(B_48), A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.62/1.42  tff(c_134, plain, (![B_53]: (k7_relat_1(B_53, k1_relat_1(B_53))=B_53 | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_52, c_109])).
% 2.62/1.42  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.42  tff(c_140, plain, (![B_53]: (k9_relat_1(B_53, k1_relat_1(B_53))=k2_relat_1(B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_134, c_10])).
% 2.62/1.42  tff(c_239, plain, (![A_73, B_74, C_75, D_76]: (k8_relset_1(A_73, B_74, C_75, D_76)=k10_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.42  tff(c_249, plain, (![D_76]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_76)=k10_relat_1('#skF_3', D_76))), inference(resolution, [status(thm)], [c_32, c_239])).
% 2.62/1.42  tff(c_177, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.42  tff(c_190, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_177])).
% 2.62/1.42  tff(c_289, plain, (![A_88, B_89, C_90]: (k8_relset_1(A_88, B_89, C_90, B_89)=k1_relset_1(A_88, B_89, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.42  tff(c_294, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_289])).
% 2.62/1.42  tff(c_300, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_190, c_294])).
% 2.62/1.42  tff(c_205, plain, (![A_65, B_66, C_67, D_68]: (k7_relset_1(A_65, B_66, C_67, D_68)=k9_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.42  tff(c_215, plain, (![D_68]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_68)=k9_relat_1('#skF_3', D_68))), inference(resolution, [status(thm)], [c_32, c_205])).
% 2.62/1.42  tff(c_115, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.42  tff(c_128, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_115])).
% 2.62/1.42  tff(c_30, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.42  tff(c_74, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.62/1.42  tff(c_155, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_74])).
% 2.62/1.42  tff(c_217, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_155])).
% 2.62/1.42  tff(c_251, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_217])).
% 2.62/1.42  tff(c_303, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_251])).
% 2.62/1.42  tff(c_310, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_303])).
% 2.62/1.42  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_310])).
% 2.62/1.42  tff(c_315, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.62/1.42  tff(c_442, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_315])).
% 2.62/1.42  tff(c_488, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_442])).
% 2.62/1.42  tff(c_532, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_530, c_488])).
% 2.62/1.42  tff(c_639, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_532])).
% 2.62/1.42  tff(c_646, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_639])).
% 2.62/1.42  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_646])).
% 2.62/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.42  
% 2.62/1.42  Inference rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Ref     : 0
% 2.62/1.42  #Sup     : 139
% 2.62/1.42  #Fact    : 0
% 2.62/1.42  #Define  : 0
% 2.62/1.42  #Split   : 1
% 2.62/1.42  #Chain   : 0
% 2.62/1.42  #Close   : 0
% 2.62/1.42  
% 2.62/1.42  Ordering : KBO
% 2.62/1.42  
% 2.62/1.42  Simplification rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Subsume      : 0
% 2.62/1.42  #Demod        : 53
% 2.62/1.42  #Tautology    : 92
% 2.62/1.42  #SimpNegUnit  : 0
% 2.62/1.42  #BackRed      : 9
% 2.62/1.42  
% 2.62/1.42  #Partial instantiations: 0
% 2.62/1.42  #Strategies tried      : 1
% 2.62/1.42  
% 2.62/1.42  Timing (in seconds)
% 2.62/1.42  ----------------------
% 2.62/1.42  Preprocessing        : 0.32
% 2.62/1.42  Parsing              : 0.18
% 2.62/1.42  CNF conversion       : 0.02
% 2.62/1.42  Main loop            : 0.28
% 2.62/1.42  Inferencing          : 0.12
% 2.62/1.42  Reduction            : 0.08
% 2.62/1.42  Demodulation         : 0.06
% 2.62/1.42  BG Simplification    : 0.02
% 2.62/1.42  Subsumption          : 0.04
% 2.62/1.42  Abstraction          : 0.02
% 2.62/1.42  MUC search           : 0.00
% 2.62/1.42  Cooper               : 0.00
% 2.62/1.42  Total                : 0.64
% 2.62/1.42  Index Insertion      : 0.00
% 2.62/1.42  Index Deletion       : 0.00
% 2.62/1.42  Index Matching       : 0.00
% 2.62/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
