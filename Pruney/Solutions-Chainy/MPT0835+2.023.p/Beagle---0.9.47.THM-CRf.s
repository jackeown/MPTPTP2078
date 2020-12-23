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
% DateTime   : Thu Dec  3 10:07:58 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 145 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 231 expanded)
%              Number of equality atoms :   52 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_31,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_8,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k7_relset_1(A_71,B_72,C_73,D_74) = k9_relat_1(C_73,D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,(
    ! [D_74] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_74) = k9_relat_1('#skF_3',D_74) ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_61,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_relset_1(A_38,B_39,C_40) = k2_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_61])).

tff(c_265,plain,(
    ! [A_81,B_82,C_83] :
      ( k7_relset_1(A_81,B_82,C_83,A_81) = k2_relset_1(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_267,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_265])).

tff(c_269,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_65,c_267])).

tff(c_245,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k8_relset_1(A_76,B_77,C_78,D_79) = k10_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,(
    ! [D_79] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_79) = k10_relat_1('#skF_3',D_79) ),
    inference(resolution,[status(thm)],[c_28,c_245])).

tff(c_87,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k8_relset_1(A_46,B_47,C_48,D_49) = k10_relat_1(C_48,D_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [D_49] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_49) = k10_relat_1('#skF_3',D_49) ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_52,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_101,plain,(
    ! [A_51,B_52,C_53] :
      ( k8_relset_1(A_51,B_52,C_53,B_52) = k1_relset_1(A_51,B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_103,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_105,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_56,c_103])).

tff(c_73,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k7_relset_1(A_41,B_42,C_43,D_44) = k9_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [D_44] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_44) = k9_relat_1('#skF_3',D_44) ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_26,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_26])).

tff(c_67,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_67])).

tff(c_77,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72])).

tff(c_91,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_77])).

tff(c_106,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_91])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [D_57,B_58,C_59,A_60] :
      ( m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(B_58,C_59)))
      | ~ r1_tarski(k1_relat_1(D_57),B_58)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_60,C_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    ! [B_61] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_61,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_61) ) ),
    inference(resolution,[status(thm)],[c_28,c_120])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k7_relset_1(A_13,B_14,C_15,D_16) = k9_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_187,plain,(
    ! [B_67,D_68] :
      ( k7_relset_1(B_67,'#skF_1','#skF_3',D_68) = k9_relat_1('#skF_3',D_68)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_67) ) ),
    inference(resolution,[status(thm)],[c_124,c_16])).

tff(c_191,plain,(
    ! [D_68] : k7_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',D_68) = k9_relat_1('#skF_3',D_68) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [B_62] :
      ( k2_relset_1(B_62,'#skF_1','#skF_3') = k2_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_62) ) ),
    inference(resolution,[status(thm)],[c_124,c_14])).

tff(c_158,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_24,plain,(
    ! [A_25,B_26,C_27] :
      ( k7_relset_1(A_25,B_26,C_27,A_25) = k2_relset_1(A_25,B_26,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_201,plain,(
    ! [B_70] :
      ( k7_relset_1(B_70,'#skF_1','#skF_3',B_70) = k2_relset_1(B_70,'#skF_1','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_70) ) ),
    inference(resolution,[status(thm)],[c_124,c_24])).

tff(c_204,plain,(
    k7_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',k1_relat_1('#skF_3')) = k2_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_201])).

tff(c_206,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_158,c_204])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_206])).

tff(c_209,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_228,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_209])).

tff(c_251,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_228])).

tff(c_270,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_251])).

tff(c_277,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_270])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.28  
% 2.13/1.28  %Foreground sorts:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Background operators:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Foreground operators:
% 2.13/1.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.28  
% 2.13/1.30  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.13/1.30  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.13/1.30  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.13/1.30  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.13/1.30  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.13/1.30  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.13/1.30  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.13/1.30  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.13/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.30  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.13/1.30  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_31, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.30  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.13/1.30  tff(c_8, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.30  tff(c_215, plain, (![A_71, B_72, C_73, D_74]: (k7_relset_1(A_71, B_72, C_73, D_74)=k9_relat_1(C_73, D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.30  tff(c_218, plain, (![D_74]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_74)=k9_relat_1('#skF_3', D_74))), inference(resolution, [status(thm)], [c_28, c_215])).
% 2.13/1.30  tff(c_61, plain, (![A_38, B_39, C_40]: (k2_relset_1(A_38, B_39, C_40)=k2_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.30  tff(c_65, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_61])).
% 2.13/1.30  tff(c_265, plain, (![A_81, B_82, C_83]: (k7_relset_1(A_81, B_82, C_83, A_81)=k2_relset_1(A_81, B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.30  tff(c_267, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_265])).
% 2.13/1.30  tff(c_269, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_65, c_267])).
% 2.13/1.30  tff(c_245, plain, (![A_76, B_77, C_78, D_79]: (k8_relset_1(A_76, B_77, C_78, D_79)=k10_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.30  tff(c_248, plain, (![D_79]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_79)=k10_relat_1('#skF_3', D_79))), inference(resolution, [status(thm)], [c_28, c_245])).
% 2.13/1.30  tff(c_87, plain, (![A_46, B_47, C_48, D_49]: (k8_relset_1(A_46, B_47, C_48, D_49)=k10_relat_1(C_48, D_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.30  tff(c_90, plain, (![D_49]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_49)=k10_relat_1('#skF_3', D_49))), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.13/1.30  tff(c_52, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.30  tff(c_56, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.13/1.30  tff(c_101, plain, (![A_51, B_52, C_53]: (k8_relset_1(A_51, B_52, C_53, B_52)=k1_relset_1(A_51, B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.30  tff(c_103, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_101])).
% 2.13/1.30  tff(c_105, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_56, c_103])).
% 2.13/1.30  tff(c_73, plain, (![A_41, B_42, C_43, D_44]: (k7_relset_1(A_41, B_42, C_43, D_44)=k9_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.30  tff(c_76, plain, (![D_44]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_44)=k9_relat_1('#skF_3', D_44))), inference(resolution, [status(thm)], [c_28, c_73])).
% 2.13/1.30  tff(c_26, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_66, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_26])).
% 2.13/1.30  tff(c_67, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 2.13/1.30  tff(c_72, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_67])).
% 2.13/1.30  tff(c_77, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72])).
% 2.13/1.30  tff(c_91, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_77])).
% 2.13/1.30  tff(c_106, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_91])).
% 2.13/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_120, plain, (![D_57, B_58, C_59, A_60]: (m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(B_58, C_59))) | ~r1_tarski(k1_relat_1(D_57), B_58) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_60, C_59))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.30  tff(c_124, plain, (![B_61]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_61, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_61))), inference(resolution, [status(thm)], [c_28, c_120])).
% 2.13/1.30  tff(c_16, plain, (![A_13, B_14, C_15, D_16]: (k7_relset_1(A_13, B_14, C_15, D_16)=k9_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.30  tff(c_187, plain, (![B_67, D_68]: (k7_relset_1(B_67, '#skF_1', '#skF_3', D_68)=k9_relat_1('#skF_3', D_68) | ~r1_tarski(k1_relat_1('#skF_3'), B_67))), inference(resolution, [status(thm)], [c_124, c_16])).
% 2.13/1.30  tff(c_191, plain, (![D_68]: (k7_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', D_68)=k9_relat_1('#skF_3', D_68))), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.13/1.30  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.30  tff(c_153, plain, (![B_62]: (k2_relset_1(B_62, '#skF_1', '#skF_3')=k2_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_62))), inference(resolution, [status(thm)], [c_124, c_14])).
% 2.13/1.30  tff(c_158, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_153])).
% 2.13/1.30  tff(c_24, plain, (![A_25, B_26, C_27]: (k7_relset_1(A_25, B_26, C_27, A_25)=k2_relset_1(A_25, B_26, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.30  tff(c_201, plain, (![B_70]: (k7_relset_1(B_70, '#skF_1', '#skF_3', B_70)=k2_relset_1(B_70, '#skF_1', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_70))), inference(resolution, [status(thm)], [c_124, c_24])).
% 2.13/1.30  tff(c_204, plain, (k7_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', k1_relat_1('#skF_3'))=k2_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_201])).
% 2.13/1.30  tff(c_206, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_158, c_204])).
% 2.13/1.30  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_206])).
% 2.13/1.30  tff(c_209, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 2.13/1.30  tff(c_228, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_209])).
% 2.13/1.30  tff(c_251, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_228])).
% 2.13/1.30  tff(c_270, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_251])).
% 2.13/1.30  tff(c_277, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_270])).
% 2.13/1.30  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_277])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 64
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 1
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 1
% 2.13/1.30  #Demod        : 24
% 2.13/1.30  #Tautology    : 40
% 2.13/1.30  #SimpNegUnit  : 1
% 2.13/1.30  #BackRed      : 7
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.28
% 2.13/1.30  Parsing              : 0.15
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.19
% 2.13/1.30  Inferencing          : 0.07
% 2.13/1.30  Reduction            : 0.06
% 2.13/1.30  Demodulation         : 0.04
% 2.13/1.30  BG Simplification    : 0.01
% 2.13/1.30  Subsumption          : 0.03
% 2.13/1.30  Abstraction          : 0.01
% 2.13/1.30  MUC search           : 0.00
% 2.13/1.30  Cooper               : 0.00
% 2.13/1.30  Total                : 0.51
% 2.13/1.30  Index Insertion      : 0.00
% 2.13/1.30  Index Deletion       : 0.00
% 2.13/1.30  Index Matching       : 0.00
% 2.13/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
