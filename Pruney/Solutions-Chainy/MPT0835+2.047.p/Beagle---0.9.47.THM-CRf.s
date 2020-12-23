%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:02 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 181 expanded)
%              Number of leaves         :   30 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  144 ( 328 expanded)
%              Number of equality atoms :   64 ( 139 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_476,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k7_relset_1(A_129,B_130,C_131,D_132) = k9_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_479,plain,(
    ! [D_132] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_132) = k9_relat_1('#skF_3',D_132) ),
    inference(resolution,[status(thm)],[c_30,c_476])).

tff(c_48,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_532,plain,(
    ! [A_137,B_138,C_139] :
      ( k7_relset_1(A_137,B_138,C_139,A_137) = k2_relset_1(A_137,B_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_534,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_532])).

tff(c_536,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_52,c_534])).

tff(c_461,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k8_relset_1(A_124,B_125,C_126,D_127) = k10_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_464,plain,(
    ! [D_127] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_127) = k10_relat_1('#skF_3',D_127) ),
    inference(resolution,[status(thm)],[c_30,c_461])).

tff(c_57,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_37,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_37])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [C_61,A_62,B_63] :
      ( m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ r1_tarski(k2_relat_1(C_61),B_63)
      | ~ r1_tarski(k1_relat_1(C_61),A_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [A_29,B_30,C_31] :
      ( k7_relset_1(A_29,B_30,C_31,A_29) = k2_relset_1(A_29,B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_394,plain,(
    ! [A_116,B_117,C_118] :
      ( k7_relset_1(A_116,B_117,C_118,A_116) = k2_relset_1(A_116,B_117,C_118)
      | ~ r1_tarski(k2_relat_1(C_118),B_117)
      | ~ r1_tarski(k1_relat_1(C_118),A_116)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_399,plain,(
    ! [A_119,C_120] :
      ( k7_relset_1(A_119,k2_relat_1(C_120),C_120,A_119) = k2_relset_1(A_119,k2_relat_1(C_120),C_120)
      | ~ r1_tarski(k1_relat_1(C_120),A_119)
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_394])).

tff(c_404,plain,(
    ! [C_121] :
      ( k7_relset_1(k1_relat_1(C_121),k2_relat_1(C_121),C_121,k1_relat_1(C_121)) = k2_relset_1(k1_relat_1(C_121),k2_relat_1(C_121),C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_399])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k7_relset_1(A_14,B_15,C_16,D_17) = k9_relat_1(C_16,D_17)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_292,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ r1_tarski(k2_relat_1(C_100),B_99)
      | ~ r1_tarski(k1_relat_1(C_100),A_98)
      | ~ v1_relat_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_115,c_16])).

tff(c_306,plain,(
    ! [A_104,C_105,D_106] :
      ( k7_relset_1(A_104,k2_relat_1(C_105),C_105,D_106) = k9_relat_1(C_105,D_106)
      | ~ r1_tarski(k1_relat_1(C_105),A_104)
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_292])).

tff(c_310,plain,(
    ! [C_105,D_106] :
      ( k7_relset_1(k1_relat_1(C_105),k2_relat_1(C_105),C_105,D_106) = k9_relat_1(C_105,D_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_306])).

tff(c_420,plain,(
    ! [C_122] :
      ( k2_relset_1(k1_relat_1(C_122),k2_relat_1(C_122),C_122) = k9_relat_1(C_122,k1_relat_1(C_122))
      | ~ v1_relat_1(C_122)
      | ~ v1_relat_1(C_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_310])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_263,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ r1_tarski(k2_relat_1(C_87),B_86)
      | ~ r1_tarski(k1_relat_1(C_87),A_85)
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_115,c_14])).

tff(c_268,plain,(
    ! [A_88,C_89] :
      ( k2_relset_1(A_88,k2_relat_1(C_89),C_89) = k2_relat_1(C_89)
      | ~ r1_tarski(k1_relat_1(C_89),A_88)
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_263])).

tff(c_272,plain,(
    ! [C_89] :
      ( k2_relset_1(k1_relat_1(C_89),k2_relat_1(C_89),C_89) = k2_relat_1(C_89)
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_435,plain,(
    ! [C_123] :
      ( k9_relat_1(C_123,k1_relat_1(C_123)) = k2_relat_1(C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_272])).

tff(c_68,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k8_relset_1(A_45,B_46,C_47,D_48) = k10_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    ! [D_48] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_48) = k10_relat_1('#skF_3',D_48) ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_105,plain,(
    ! [A_58,B_59,C_60] :
      ( k8_relset_1(A_58,B_59,C_60,B_59) = k1_relset_1(A_58,B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_107,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_109,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_61,c_107])).

tff(c_82,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k7_relset_1(A_50,B_51,C_52,D_53) = k9_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    ! [D_53] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_53) = k9_relat_1('#skF_3',D_53) ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_28,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_62,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_63,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_72,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_63])).

tff(c_86,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_72])).

tff(c_110,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_86])).

tff(c_441,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_110])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_441])).

tff(c_450,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_460,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_450])).

tff(c_465,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_460])).

tff(c_504,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_465])).

tff(c_537,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_504])).

tff(c_542,plain,(
    ! [D_140,C_141,B_142,A_143] :
      ( m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(C_141,B_142)))
      | ~ r1_tarski(k2_relat_1(D_140),B_142)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(C_141,A_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_546,plain,(
    ! [B_144] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_144)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_144) ) ),
    inference(resolution,[status(thm)],[c_30,c_542])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k8_relset_1(A_18,B_19,C_20,D_21) = k10_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_640,plain,(
    ! [B_153,D_154] :
      ( k8_relset_1('#skF_2',B_153,'#skF_3',D_154) = k10_relat_1('#skF_3',D_154)
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_153) ) ),
    inference(resolution,[status(thm)],[c_546,c_18])).

tff(c_644,plain,(
    ! [D_154] : k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',D_154) = k10_relat_1('#skF_3',D_154) ),
    inference(resolution,[status(thm)],[c_6,c_640])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_576,plain,(
    ! [B_145] :
      ( k1_relset_1('#skF_2',B_145,'#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_145) ) ),
    inference(resolution,[status(thm)],[c_546,c_12])).

tff(c_581,plain,(
    k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_576])).

tff(c_24,plain,(
    ! [A_29,B_30,C_31] :
      ( k8_relset_1(A_29,B_30,C_31,B_30) = k1_relset_1(A_29,B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_661,plain,(
    ! [B_157] :
      ( k8_relset_1('#skF_2',B_157,'#skF_3',B_157) = k1_relset_1('#skF_2',B_157,'#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_157) ) ),
    inference(resolution,[status(thm)],[c_546,c_24])).

tff(c_664,plain,(
    k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_661])).

tff(c_666,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_581,c_664])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.81/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.81/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.81/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.45  
% 2.92/1.47  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.92/1.47  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.92/1.47  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.92/1.47  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.92/1.47  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.92/1.47  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.92/1.47  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.92/1.47  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.92/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.47  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.92/1.47  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.92/1.47  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.47  tff(c_476, plain, (![A_129, B_130, C_131, D_132]: (k7_relset_1(A_129, B_130, C_131, D_132)=k9_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.47  tff(c_479, plain, (![D_132]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_132)=k9_relat_1('#skF_3', D_132))), inference(resolution, [status(thm)], [c_30, c_476])).
% 2.92/1.47  tff(c_48, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.47  tff(c_52, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_48])).
% 2.92/1.47  tff(c_532, plain, (![A_137, B_138, C_139]: (k7_relset_1(A_137, B_138, C_139, A_137)=k2_relset_1(A_137, B_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.47  tff(c_534, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_532])).
% 2.92/1.47  tff(c_536, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_52, c_534])).
% 2.92/1.47  tff(c_461, plain, (![A_124, B_125, C_126, D_127]: (k8_relset_1(A_124, B_125, C_126, D_127)=k10_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.47  tff(c_464, plain, (![D_127]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_127)=k10_relat_1('#skF_3', D_127))), inference(resolution, [status(thm)], [c_30, c_461])).
% 2.92/1.47  tff(c_57, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.47  tff(c_61, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.92/1.47  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.92/1.47  tff(c_34, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.92/1.47  tff(c_37, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_34])).
% 2.92/1.47  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_37])).
% 2.92/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.47  tff(c_115, plain, (![C_61, A_62, B_63]: (m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~r1_tarski(k2_relat_1(C_61), B_63) | ~r1_tarski(k1_relat_1(C_61), A_62) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.92/1.47  tff(c_26, plain, (![A_29, B_30, C_31]: (k7_relset_1(A_29, B_30, C_31, A_29)=k2_relset_1(A_29, B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.47  tff(c_394, plain, (![A_116, B_117, C_118]: (k7_relset_1(A_116, B_117, C_118, A_116)=k2_relset_1(A_116, B_117, C_118) | ~r1_tarski(k2_relat_1(C_118), B_117) | ~r1_tarski(k1_relat_1(C_118), A_116) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_115, c_26])).
% 2.92/1.47  tff(c_399, plain, (![A_119, C_120]: (k7_relset_1(A_119, k2_relat_1(C_120), C_120, A_119)=k2_relset_1(A_119, k2_relat_1(C_120), C_120) | ~r1_tarski(k1_relat_1(C_120), A_119) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_6, c_394])).
% 2.92/1.47  tff(c_404, plain, (![C_121]: (k7_relset_1(k1_relat_1(C_121), k2_relat_1(C_121), C_121, k1_relat_1(C_121))=k2_relset_1(k1_relat_1(C_121), k2_relat_1(C_121), C_121) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_6, c_399])).
% 2.92/1.47  tff(c_16, plain, (![A_14, B_15, C_16, D_17]: (k7_relset_1(A_14, B_15, C_16, D_17)=k9_relat_1(C_16, D_17) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.47  tff(c_292, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~r1_tarski(k2_relat_1(C_100), B_99) | ~r1_tarski(k1_relat_1(C_100), A_98) | ~v1_relat_1(C_100))), inference(resolution, [status(thm)], [c_115, c_16])).
% 2.92/1.47  tff(c_306, plain, (![A_104, C_105, D_106]: (k7_relset_1(A_104, k2_relat_1(C_105), C_105, D_106)=k9_relat_1(C_105, D_106) | ~r1_tarski(k1_relat_1(C_105), A_104) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_6, c_292])).
% 2.92/1.47  tff(c_310, plain, (![C_105, D_106]: (k7_relset_1(k1_relat_1(C_105), k2_relat_1(C_105), C_105, D_106)=k9_relat_1(C_105, D_106) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_6, c_306])).
% 2.92/1.47  tff(c_420, plain, (![C_122]: (k2_relset_1(k1_relat_1(C_122), k2_relat_1(C_122), C_122)=k9_relat_1(C_122, k1_relat_1(C_122)) | ~v1_relat_1(C_122) | ~v1_relat_1(C_122))), inference(superposition, [status(thm), theory('equality')], [c_404, c_310])).
% 2.92/1.47  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.47  tff(c_263, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~r1_tarski(k2_relat_1(C_87), B_86) | ~r1_tarski(k1_relat_1(C_87), A_85) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_115, c_14])).
% 2.92/1.47  tff(c_268, plain, (![A_88, C_89]: (k2_relset_1(A_88, k2_relat_1(C_89), C_89)=k2_relat_1(C_89) | ~r1_tarski(k1_relat_1(C_89), A_88) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_6, c_263])).
% 2.92/1.47  tff(c_272, plain, (![C_89]: (k2_relset_1(k1_relat_1(C_89), k2_relat_1(C_89), C_89)=k2_relat_1(C_89) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.92/1.47  tff(c_435, plain, (![C_123]: (k9_relat_1(C_123, k1_relat_1(C_123))=k2_relat_1(C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(C_123))), inference(superposition, [status(thm), theory('equality')], [c_420, c_272])).
% 2.92/1.47  tff(c_68, plain, (![A_45, B_46, C_47, D_48]: (k8_relset_1(A_45, B_46, C_47, D_48)=k10_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.47  tff(c_71, plain, (![D_48]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_48)=k10_relat_1('#skF_3', D_48))), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.92/1.47  tff(c_105, plain, (![A_58, B_59, C_60]: (k8_relset_1(A_58, B_59, C_60, B_59)=k1_relset_1(A_58, B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.47  tff(c_107, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_105])).
% 2.92/1.47  tff(c_109, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_61, c_107])).
% 2.92/1.47  tff(c_82, plain, (![A_50, B_51, C_52, D_53]: (k7_relset_1(A_50, B_51, C_52, D_53)=k9_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.47  tff(c_85, plain, (![D_53]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_53)=k9_relat_1('#skF_3', D_53))), inference(resolution, [status(thm)], [c_30, c_82])).
% 2.92/1.47  tff(c_28, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.47  tff(c_62, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 2.92/1.47  tff(c_63, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 2.92/1.47  tff(c_72, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_63])).
% 2.92/1.47  tff(c_86, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_72])).
% 2.92/1.47  tff(c_110, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_86])).
% 2.92/1.47  tff(c_441, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_435, c_110])).
% 2.92/1.47  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_441])).
% 2.92/1.47  tff(c_450, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 2.92/1.47  tff(c_460, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_450])).
% 2.92/1.47  tff(c_465, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_460])).
% 2.92/1.47  tff(c_504, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_465])).
% 2.92/1.47  tff(c_537, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_536, c_504])).
% 2.92/1.47  tff(c_542, plain, (![D_140, C_141, B_142, A_143]: (m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(C_141, B_142))) | ~r1_tarski(k2_relat_1(D_140), B_142) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(C_141, A_143))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.92/1.47  tff(c_546, plain, (![B_144]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_144))) | ~r1_tarski(k2_relat_1('#skF_3'), B_144))), inference(resolution, [status(thm)], [c_30, c_542])).
% 2.92/1.47  tff(c_18, plain, (![A_18, B_19, C_20, D_21]: (k8_relset_1(A_18, B_19, C_20, D_21)=k10_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.47  tff(c_640, plain, (![B_153, D_154]: (k8_relset_1('#skF_2', B_153, '#skF_3', D_154)=k10_relat_1('#skF_3', D_154) | ~r1_tarski(k2_relat_1('#skF_3'), B_153))), inference(resolution, [status(thm)], [c_546, c_18])).
% 2.92/1.47  tff(c_644, plain, (![D_154]: (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', D_154)=k10_relat_1('#skF_3', D_154))), inference(resolution, [status(thm)], [c_6, c_640])).
% 2.92/1.47  tff(c_12, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.47  tff(c_576, plain, (![B_145]: (k1_relset_1('#skF_2', B_145, '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), B_145))), inference(resolution, [status(thm)], [c_546, c_12])).
% 2.92/1.47  tff(c_581, plain, (k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_576])).
% 2.92/1.47  tff(c_24, plain, (![A_29, B_30, C_31]: (k8_relset_1(A_29, B_30, C_31, B_30)=k1_relset_1(A_29, B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.47  tff(c_661, plain, (![B_157]: (k8_relset_1('#skF_2', B_157, '#skF_3', B_157)=k1_relset_1('#skF_2', B_157, '#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), B_157))), inference(resolution, [status(thm)], [c_546, c_24])).
% 2.92/1.47  tff(c_664, plain, (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_661])).
% 2.92/1.47  tff(c_666, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_581, c_664])).
% 2.92/1.47  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_537, c_666])).
% 2.92/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.47  
% 2.92/1.47  Inference rules
% 2.92/1.47  ----------------------
% 2.92/1.47  #Ref     : 0
% 2.92/1.47  #Sup     : 156
% 2.92/1.47  #Fact    : 0
% 2.92/1.47  #Define  : 0
% 2.92/1.47  #Split   : 1
% 2.92/1.47  #Chain   : 0
% 2.92/1.47  #Close   : 0
% 2.92/1.47  
% 2.92/1.47  Ordering : KBO
% 2.92/1.47  
% 2.92/1.47  Simplification rules
% 2.92/1.47  ----------------------
% 2.92/1.47  #Subsume      : 6
% 2.92/1.47  #Demod        : 54
% 2.92/1.47  #Tautology    : 84
% 2.92/1.47  #SimpNegUnit  : 1
% 2.92/1.47  #BackRed      : 8
% 2.92/1.47  
% 2.92/1.47  #Partial instantiations: 0
% 2.92/1.47  #Strategies tried      : 1
% 2.92/1.47  
% 2.92/1.47  Timing (in seconds)
% 2.92/1.47  ----------------------
% 2.92/1.47  Preprocessing        : 0.32
% 2.92/1.47  Parsing              : 0.18
% 2.92/1.47  CNF conversion       : 0.02
% 2.92/1.47  Main loop            : 0.32
% 2.92/1.47  Inferencing          : 0.12
% 2.92/1.47  Reduction            : 0.09
% 2.92/1.47  Demodulation         : 0.07
% 2.92/1.47  BG Simplification    : 0.02
% 2.92/1.47  Subsumption          : 0.05
% 2.92/1.47  Abstraction          : 0.02
% 2.92/1.47  MUC search           : 0.00
% 2.92/1.47  Cooper               : 0.00
% 2.92/1.47  Total                : 0.68
% 2.92/1.47  Index Insertion      : 0.00
% 2.92/1.47  Index Deletion       : 0.00
% 2.92/1.47  Index Matching       : 0.00
% 2.92/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
