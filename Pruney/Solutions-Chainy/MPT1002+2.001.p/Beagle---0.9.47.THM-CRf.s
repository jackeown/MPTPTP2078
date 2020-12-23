%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 187 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 494 expanded)
%              Number of equality atoms :   41 ( 192 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_43,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_61])).

tff(c_101,plain,(
    ! [B_49,A_50,C_51] :
      ( k1_xboole_0 = B_49
      | k1_relset_1(A_50,B_49,C_51) = A_50
      | ~ v1_funct_2(C_51,A_50,B_49)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_65,c_104])).

tff(c_108,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_107])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,k10_relat_1(C_56,B_57))
      | ~ r1_tarski(k9_relat_1(C_56,A_55),B_57)
      | ~ r1_tarski(A_55,k1_relat_1(C_56))
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_58,C_59] :
      ( r1_tarski(A_58,k10_relat_1(C_59,k9_relat_1(C_59,A_58)))
      | ~ r1_tarski(A_58,k1_relat_1(C_59))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_84,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k7_relset_1(A_38,B_39,C_40,D_41) = k9_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [D_41] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_41) = k9_relat_1('#skF_4',D_41) ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_66,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k8_relset_1(A_33,B_34,C_35,D_36) = k10_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    ! [D_36] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_36) = k10_relat_1('#skF_4',D_36) ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_74,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_30])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_74])).

tff(c_139,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_88])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_40,c_34,c_108,c_139])).

tff(c_147,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_153,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_148])).

tff(c_159,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_36])).

tff(c_160,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_160])).

tff(c_154,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_38])).

tff(c_179,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_183,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_179])).

tff(c_26,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_233,plain,(
    ! [B_83,C_84] :
      ( k1_relset_1('#skF_1',B_83,C_84) = '#skF_1'
      | ~ v1_funct_2(C_84,'#skF_1',B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_147,c_147,c_147,c_26])).

tff(c_236,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_159,c_233])).

tff(c_239,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_183,c_236])).

tff(c_267,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(A_91,k10_relat_1(C_92,B_93))
      | ~ r1_tarski(k9_relat_1(C_92,A_91),B_93)
      | ~ r1_tarski(A_91,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    ! [A_94,C_95] :
      ( r1_tarski(A_94,k10_relat_1(C_95,k9_relat_1(C_95,A_94)))
      | ~ r1_tarski(A_94,k1_relat_1(C_95))
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_211,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_relset_1(A_76,B_77,C_78,D_79) = k9_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,(
    ! [D_79] : k7_relset_1('#skF_1','#skF_1','#skF_4',D_79) = k9_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_159,c_211])).

tff(c_188,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k8_relset_1(A_69,B_70,C_71,D_72) = k10_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_191,plain,(
    ! [D_72] : k8_relset_1('#skF_1','#skF_1','#skF_4',D_72) = k10_relat_1('#skF_4',D_72) ),
    inference(resolution,[status(thm)],[c_159,c_188])).

tff(c_176,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_30])).

tff(c_201,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_176])).

tff(c_215,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_201])).

tff(c_280,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_273,c_215])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_40,c_34,c_239,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.34  
% 2.09/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.34  
% 2.09/1.34  %Foreground sorts:
% 2.09/1.34  
% 2.09/1.34  
% 2.09/1.34  %Background operators:
% 2.09/1.34  
% 2.09/1.34  
% 2.09/1.34  %Foreground operators:
% 2.09/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.09/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.09/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.09/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.09/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.34  
% 2.43/1.36  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 2.43/1.36  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.43/1.36  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.43/1.36  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.43/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.36  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.43/1.36  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.43/1.36  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.43/1.36  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.36  tff(c_55, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.36  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.43/1.36  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.36  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.36  tff(c_32, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.36  tff(c_43, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.43/1.36  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.36  tff(c_61, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.36  tff(c_65, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_61])).
% 2.43/1.36  tff(c_101, plain, (![B_49, A_50, C_51]: (k1_xboole_0=B_49 | k1_relset_1(A_50, B_49, C_51)=A_50 | ~v1_funct_2(C_51, A_50, B_49) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.36  tff(c_104, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_101])).
% 2.43/1.36  tff(c_107, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_65, c_104])).
% 2.43/1.36  tff(c_108, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_43, c_107])).
% 2.43/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.36  tff(c_126, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, k10_relat_1(C_56, B_57)) | ~r1_tarski(k9_relat_1(C_56, A_55), B_57) | ~r1_tarski(A_55, k1_relat_1(C_56)) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.36  tff(c_132, plain, (![A_58, C_59]: (r1_tarski(A_58, k10_relat_1(C_59, k9_relat_1(C_59, A_58))) | ~r1_tarski(A_58, k1_relat_1(C_59)) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_6, c_126])).
% 2.43/1.36  tff(c_84, plain, (![A_38, B_39, C_40, D_41]: (k7_relset_1(A_38, B_39, C_40, D_41)=k9_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.36  tff(c_87, plain, (![D_41]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_41)=k9_relat_1('#skF_4', D_41))), inference(resolution, [status(thm)], [c_36, c_84])).
% 2.43/1.36  tff(c_66, plain, (![A_33, B_34, C_35, D_36]: (k8_relset_1(A_33, B_34, C_35, D_36)=k10_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.36  tff(c_69, plain, (![D_36]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_36)=k10_relat_1('#skF_4', D_36))), inference(resolution, [status(thm)], [c_36, c_66])).
% 2.43/1.36  tff(c_30, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.36  tff(c_74, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_30])).
% 2.43/1.36  tff(c_88, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_74])).
% 2.43/1.36  tff(c_139, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_88])).
% 2.43/1.36  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_40, c_34, c_108, c_139])).
% 2.43/1.36  tff(c_147, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.43/1.36  tff(c_148, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.43/1.36  tff(c_153, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_148])).
% 2.43/1.36  tff(c_159, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_36])).
% 2.43/1.36  tff(c_160, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.36  tff(c_164, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_159, c_160])).
% 2.43/1.36  tff(c_154, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_38])).
% 2.43/1.36  tff(c_179, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.36  tff(c_183, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_159, c_179])).
% 2.43/1.36  tff(c_26, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.36  tff(c_233, plain, (![B_83, C_84]: (k1_relset_1('#skF_1', B_83, C_84)='#skF_1' | ~v1_funct_2(C_84, '#skF_1', B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_83))))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_147, c_147, c_147, c_26])).
% 2.43/1.36  tff(c_236, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_159, c_233])).
% 2.43/1.36  tff(c_239, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_183, c_236])).
% 2.43/1.36  tff(c_267, plain, (![A_91, C_92, B_93]: (r1_tarski(A_91, k10_relat_1(C_92, B_93)) | ~r1_tarski(k9_relat_1(C_92, A_91), B_93) | ~r1_tarski(A_91, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.36  tff(c_273, plain, (![A_94, C_95]: (r1_tarski(A_94, k10_relat_1(C_95, k9_relat_1(C_95, A_94))) | ~r1_tarski(A_94, k1_relat_1(C_95)) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(resolution, [status(thm)], [c_6, c_267])).
% 2.43/1.36  tff(c_211, plain, (![A_76, B_77, C_78, D_79]: (k7_relset_1(A_76, B_77, C_78, D_79)=k9_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.36  tff(c_214, plain, (![D_79]: (k7_relset_1('#skF_1', '#skF_1', '#skF_4', D_79)=k9_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_159, c_211])).
% 2.43/1.36  tff(c_188, plain, (![A_69, B_70, C_71, D_72]: (k8_relset_1(A_69, B_70, C_71, D_72)=k10_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.36  tff(c_191, plain, (![D_72]: (k8_relset_1('#skF_1', '#skF_1', '#skF_4', D_72)=k10_relat_1('#skF_4', D_72))), inference(resolution, [status(thm)], [c_159, c_188])).
% 2.43/1.36  tff(c_176, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_30])).
% 2.43/1.36  tff(c_201, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_176])).
% 2.43/1.36  tff(c_215, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_201])).
% 2.43/1.36  tff(c_280, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_273, c_215])).
% 2.43/1.36  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_40, c_34, c_239, c_280])).
% 2.43/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  Inference rules
% 2.43/1.36  ----------------------
% 2.43/1.36  #Ref     : 0
% 2.43/1.36  #Sup     : 51
% 2.43/1.36  #Fact    : 0
% 2.43/1.36  #Define  : 0
% 2.43/1.36  #Split   : 3
% 2.43/1.36  #Chain   : 0
% 2.43/1.36  #Close   : 0
% 2.43/1.36  
% 2.43/1.36  Ordering : KBO
% 2.43/1.36  
% 2.43/1.36  Simplification rules
% 2.43/1.36  ----------------------
% 2.43/1.36  #Subsume      : 0
% 2.43/1.36  #Demod        : 54
% 2.43/1.36  #Tautology    : 32
% 2.43/1.36  #SimpNegUnit  : 2
% 2.43/1.36  #BackRed      : 7
% 2.43/1.36  
% 2.43/1.36  #Partial instantiations: 0
% 2.43/1.36  #Strategies tried      : 1
% 2.43/1.36  
% 2.43/1.36  Timing (in seconds)
% 2.43/1.36  ----------------------
% 2.43/1.36  Preprocessing        : 0.31
% 2.43/1.36  Parsing              : 0.16
% 2.43/1.36  CNF conversion       : 0.02
% 2.43/1.36  Main loop            : 0.21
% 2.43/1.36  Inferencing          : 0.08
% 2.43/1.36  Reduction            : 0.07
% 2.43/1.36  Demodulation         : 0.05
% 2.43/1.36  BG Simplification    : 0.01
% 2.43/1.36  Subsumption          : 0.03
% 2.43/1.36  Abstraction          : 0.01
% 2.43/1.36  MUC search           : 0.00
% 2.43/1.36  Cooper               : 0.00
% 2.43/1.36  Total                : 0.56
% 2.43/1.36  Index Insertion      : 0.00
% 2.43/1.36  Index Deletion       : 0.00
% 2.43/1.36  Index Matching       : 0.00
% 2.43/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
