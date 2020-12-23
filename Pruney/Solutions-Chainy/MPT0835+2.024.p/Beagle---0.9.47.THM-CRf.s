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
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 145 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   10
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_129,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k7_relset_1(A_54,B_55,C_56,D_57) = k9_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [D_57] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_57) = k9_relat_1('#skF_3',D_57) ),
    inference(resolution,[status(thm)],[c_28,c_129])).

tff(c_61,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_relset_1(A_38,B_39,C_40) = k2_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_61])).

tff(c_209,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_relset_1(A_67,B_68,C_69,A_67) = k2_relset_1(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_211,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_209])).

tff(c_213,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_65,c_211])).

tff(c_133,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k8_relset_1(A_58,B_59,C_60,D_61) = k10_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [D_61] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_61) = k10_relat_1('#skF_3',D_61) ),
    inference(resolution,[status(thm)],[c_28,c_133])).

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
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

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

tff(c_113,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_113])).

tff(c_118,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_137,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_118])).

tff(c_163,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_137])).

tff(c_214,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_163])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [D_70,C_71,B_72,A_73] :
      ( m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(C_71,B_72)))
      | ~ r1_tarski(k2_relat_1(D_70),B_72)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(C_71,A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_235,plain,(
    ! [B_74] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_74)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_74) ) ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( k8_relset_1(A_17,B_18,C_19,D_20) = k10_relat_1(C_19,D_20)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_284,plain,(
    ! [B_77,D_78] :
      ( k8_relset_1('#skF_2',B_77,'#skF_3',D_78) = k10_relat_1('#skF_3',D_78)
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_77) ) ),
    inference(resolution,[status(thm)],[c_235,c_18])).

tff(c_288,plain,(
    ! [D_78] : k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',D_78) = k10_relat_1('#skF_3',D_78) ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_274,plain,(
    ! [B_76] :
      ( k1_relset_1('#skF_2',B_76,'#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_76) ) ),
    inference(resolution,[status(thm)],[c_235,c_12])).

tff(c_279,plain,(
    k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] :
      ( k8_relset_1(A_25,B_26,C_27,B_26) = k1_relset_1(A_25,B_26,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_312,plain,(
    ! [B_83] :
      ( k8_relset_1('#skF_2',B_83,'#skF_3',B_83) = k1_relset_1('#skF_2',B_83,'#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_83) ) ),
    inference(resolution,[status(thm)],[c_235,c_22])).

tff(c_315,plain,(
    k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_312])).

tff(c_317,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_279,c_315])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.16/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.16/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.16/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.30  
% 2.16/1.32  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.16/1.32  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.16/1.32  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.16/1.32  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.16/1.32  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.16/1.32  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.16/1.32  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.16/1.32  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.16/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.32  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 2.16/1.32  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.32  tff(c_129, plain, (![A_54, B_55, C_56, D_57]: (k7_relset_1(A_54, B_55, C_56, D_57)=k9_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.32  tff(c_132, plain, (![D_57]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_57)=k9_relat_1('#skF_3', D_57))), inference(resolution, [status(thm)], [c_28, c_129])).
% 2.16/1.32  tff(c_61, plain, (![A_38, B_39, C_40]: (k2_relset_1(A_38, B_39, C_40)=k2_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.32  tff(c_65, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_61])).
% 2.16/1.32  tff(c_209, plain, (![A_67, B_68, C_69]: (k7_relset_1(A_67, B_68, C_69, A_67)=k2_relset_1(A_67, B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.32  tff(c_211, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_209])).
% 2.16/1.32  tff(c_213, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_65, c_211])).
% 2.16/1.32  tff(c_133, plain, (![A_58, B_59, C_60, D_61]: (k8_relset_1(A_58, B_59, C_60, D_61)=k10_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.32  tff(c_136, plain, (![D_61]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_61)=k10_relat_1('#skF_3', D_61))), inference(resolution, [status(thm)], [c_28, c_133])).
% 2.16/1.32  tff(c_31, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.32  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.16/1.32  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.32  tff(c_87, plain, (![A_46, B_47, C_48, D_49]: (k8_relset_1(A_46, B_47, C_48, D_49)=k10_relat_1(C_48, D_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.32  tff(c_90, plain, (![D_49]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_49)=k10_relat_1('#skF_3', D_49))), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.16/1.32  tff(c_52, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.32  tff(c_56, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.16/1.32  tff(c_101, plain, (![A_51, B_52, C_53]: (k8_relset_1(A_51, B_52, C_53, B_52)=k1_relset_1(A_51, B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.32  tff(c_103, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_101])).
% 2.16/1.32  tff(c_105, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_56, c_103])).
% 2.16/1.32  tff(c_73, plain, (![A_41, B_42, C_43, D_44]: (k7_relset_1(A_41, B_42, C_43, D_44)=k9_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.32  tff(c_76, plain, (![D_44]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_44)=k9_relat_1('#skF_3', D_44))), inference(resolution, [status(thm)], [c_28, c_73])).
% 2.16/1.32  tff(c_26, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.32  tff(c_66, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_26])).
% 2.16/1.32  tff(c_67, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 2.16/1.32  tff(c_72, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_67])).
% 2.16/1.32  tff(c_77, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72])).
% 2.16/1.32  tff(c_91, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_77])).
% 2.16/1.32  tff(c_106, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_91])).
% 2.16/1.32  tff(c_113, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 2.16/1.32  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_113])).
% 2.16/1.32  tff(c_118, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 2.16/1.32  tff(c_137, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_118])).
% 2.16/1.32  tff(c_163, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_137])).
% 2.16/1.32  tff(c_214, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_163])).
% 2.16/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.32  tff(c_231, plain, (![D_70, C_71, B_72, A_73]: (m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(C_71, B_72))) | ~r1_tarski(k2_relat_1(D_70), B_72) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(C_71, A_73))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.32  tff(c_235, plain, (![B_74]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_74))) | ~r1_tarski(k2_relat_1('#skF_3'), B_74))), inference(resolution, [status(thm)], [c_28, c_231])).
% 2.16/1.32  tff(c_18, plain, (![A_17, B_18, C_19, D_20]: (k8_relset_1(A_17, B_18, C_19, D_20)=k10_relat_1(C_19, D_20) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.32  tff(c_284, plain, (![B_77, D_78]: (k8_relset_1('#skF_2', B_77, '#skF_3', D_78)=k10_relat_1('#skF_3', D_78) | ~r1_tarski(k2_relat_1('#skF_3'), B_77))), inference(resolution, [status(thm)], [c_235, c_18])).
% 2.16/1.32  tff(c_288, plain, (![D_78]: (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', D_78)=k10_relat_1('#skF_3', D_78))), inference(resolution, [status(thm)], [c_6, c_284])).
% 2.16/1.32  tff(c_12, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.32  tff(c_274, plain, (![B_76]: (k1_relset_1('#skF_2', B_76, '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), B_76))), inference(resolution, [status(thm)], [c_235, c_12])).
% 2.16/1.32  tff(c_279, plain, (k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_274])).
% 2.16/1.32  tff(c_22, plain, (![A_25, B_26, C_27]: (k8_relset_1(A_25, B_26, C_27, B_26)=k1_relset_1(A_25, B_26, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.32  tff(c_312, plain, (![B_83]: (k8_relset_1('#skF_2', B_83, '#skF_3', B_83)=k1_relset_1('#skF_2', B_83, '#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), B_83))), inference(resolution, [status(thm)], [c_235, c_22])).
% 2.16/1.32  tff(c_315, plain, (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_312])).
% 2.16/1.32  tff(c_317, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_279, c_315])).
% 2.16/1.32  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_317])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 74
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 1
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 1
% 2.16/1.32  #Demod        : 33
% 2.16/1.32  #Tautology    : 50
% 2.16/1.32  #SimpNegUnit  : 1
% 2.16/1.32  #BackRed      : 8
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.32  Preprocessing        : 0.32
% 2.16/1.32  Parsing              : 0.17
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.20
% 2.16/1.32  Inferencing          : 0.08
% 2.16/1.32  Reduction            : 0.07
% 2.16/1.32  Demodulation         : 0.05
% 2.16/1.32  BG Simplification    : 0.01
% 2.16/1.32  Subsumption          : 0.03
% 2.16/1.32  Abstraction          : 0.01
% 2.16/1.32  MUC search           : 0.00
% 2.16/1.32  Cooper               : 0.00
% 2.16/1.32  Total                : 0.55
% 2.16/1.32  Index Insertion      : 0.00
% 2.16/1.32  Index Deletion       : 0.00
% 2.16/1.32  Index Matching       : 0.00
% 2.16/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
