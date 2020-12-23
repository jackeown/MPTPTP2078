%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:47 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 185 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_61,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_79,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_344,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_356,plain,(
    ! [C_111] :
      ( r2_relset_1('#skF_1','#skF_2',C_111,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_344])).

tff(c_359,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_356])).

tff(c_276,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_284,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_276])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_322,plain,(
    ! [A_100,B_101] :
      ( k8_relat_1(A_100,B_101) = B_101
      | ~ r1_tarski(k2_relat_1(B_101),A_100)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_327,plain,(
    ! [A_102,B_103] :
      ( k8_relat_1(A_102,B_103) = B_103
      | ~ v5_relat_1(B_103,A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_322])).

tff(c_333,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_284,c_327])).

tff(c_339,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_333])).

tff(c_28,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_26,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_360,plain,(
    ! [A_113,D_116,B_114,F_115,E_117,C_112] :
      ( k4_relset_1(A_113,B_114,C_112,D_116,E_117,F_115) = k5_relat_1(E_117,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_112,D_116)))
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_390,plain,(
    ! [A_122,B_123,A_124,E_125] :
      ( k4_relset_1(A_122,B_123,A_124,A_124,E_125,k6_partfun1(A_124)) = k5_relat_1(E_125,k6_partfun1(A_124))
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(resolution,[status(thm)],[c_26,c_360])).

tff(c_396,plain,(
    ! [A_124] : k4_relset_1('#skF_1','#skF_2',A_124,A_124,'#skF_3',k6_partfun1(A_124)) = k5_relat_1('#skF_3',k6_partfun1(A_124)) ),
    inference(resolution,[status(thm)],[c_32,c_390])).

tff(c_154,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( r2_relset_1(A_59,B_60,C_61,C_61)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_178,plain,(
    ! [C_65] :
      ( r2_relset_1('#skF_1','#skF_2',C_65,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_181,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_178])).

tff(c_59,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_10])).

tff(c_73,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_partfun1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_187,plain,(
    ! [D_73,A_70,E_74,F_72,C_69,B_71] :
      ( k4_relset_1(A_70,B_71,C_69,D_73,E_74,F_72) = k5_relat_1(E_74,F_72)
      | ~ m1_subset_1(F_72,k1_zfmisc_1(k2_zfmisc_1(C_69,D_73)))
      | ~ m1_subset_1(E_74,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_194,plain,(
    ! [A_75,B_76,E_77] :
      ( k4_relset_1(A_75,B_76,'#skF_1','#skF_2',E_77,'#skF_3') = k5_relat_1(E_77,'#skF_3')
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_32,c_187])).

tff(c_201,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_214,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_58])).

tff(c_226,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_214])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_181,c_73,c_226])).

tff(c_230,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_402,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_230])).

tff(c_414,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_402])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_359,c_339,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.31  
% 2.59/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.31  
% 2.59/1.31  %Foreground sorts:
% 2.59/1.31  
% 2.59/1.31  
% 2.59/1.31  %Background operators:
% 2.59/1.31  
% 2.59/1.31  
% 2.59/1.31  %Foreground operators:
% 2.59/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.59/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.59/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.59/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.59/1.31  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.59/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.59/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.59/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.59/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.59/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.31  
% 2.59/1.33  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.59/1.33  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.59/1.33  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.59/1.33  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.59/1.33  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.59/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.59/1.33  tff(f_79, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.59/1.33  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.59/1.33  tff(f_77, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.59/1.33  tff(f_67, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.59/1.33  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.59/1.33  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.59/1.33  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.59/1.33  tff(c_46, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.59/1.33  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.59/1.33  tff(c_344, plain, (![A_104, B_105, C_106, D_107]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.59/1.33  tff(c_356, plain, (![C_111]: (r2_relset_1('#skF_1', '#skF_2', C_111, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_344])).
% 2.59/1.33  tff(c_359, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_356])).
% 2.59/1.33  tff(c_276, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.33  tff(c_284, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_276])).
% 2.59/1.33  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.33  tff(c_322, plain, (![A_100, B_101]: (k8_relat_1(A_100, B_101)=B_101 | ~r1_tarski(k2_relat_1(B_101), A_100) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.33  tff(c_327, plain, (![A_102, B_103]: (k8_relat_1(A_102, B_103)=B_103 | ~v5_relat_1(B_103, A_102) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_4, c_322])).
% 2.59/1.33  tff(c_333, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_284, c_327])).
% 2.59/1.33  tff(c_339, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_333])).
% 2.59/1.33  tff(c_28, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.33  tff(c_6, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.33  tff(c_34, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6])).
% 2.59/1.33  tff(c_26, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.59/1.33  tff(c_360, plain, (![A_113, D_116, B_114, F_115, E_117, C_112]: (k4_relset_1(A_113, B_114, C_112, D_116, E_117, F_115)=k5_relat_1(E_117, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_112, D_116))) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.33  tff(c_390, plain, (![A_122, B_123, A_124, E_125]: (k4_relset_1(A_122, B_123, A_124, A_124, E_125, k6_partfun1(A_124))=k5_relat_1(E_125, k6_partfun1(A_124)) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(resolution, [status(thm)], [c_26, c_360])).
% 2.59/1.33  tff(c_396, plain, (![A_124]: (k4_relset_1('#skF_1', '#skF_2', A_124, A_124, '#skF_3', k6_partfun1(A_124))=k5_relat_1('#skF_3', k6_partfun1(A_124)))), inference(resolution, [status(thm)], [c_32, c_390])).
% 2.59/1.33  tff(c_154, plain, (![A_59, B_60, C_61, D_62]: (r2_relset_1(A_59, B_60, C_61, C_61) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.59/1.33  tff(c_178, plain, (![C_65]: (r2_relset_1('#skF_1', '#skF_2', C_65, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_154])).
% 2.59/1.33  tff(c_181, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_178])).
% 2.59/1.33  tff(c_59, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.33  tff(c_67, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_59])).
% 2.59/1.33  tff(c_10, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.59/1.33  tff(c_70, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_10])).
% 2.59/1.33  tff(c_73, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_70])).
% 2.59/1.33  tff(c_12, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.33  tff(c_33, plain, (![A_9, B_10]: (k5_relat_1(k6_partfun1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.59/1.33  tff(c_187, plain, (![D_73, A_70, E_74, F_72, C_69, B_71]: (k4_relset_1(A_70, B_71, C_69, D_73, E_74, F_72)=k5_relat_1(E_74, F_72) | ~m1_subset_1(F_72, k1_zfmisc_1(k2_zfmisc_1(C_69, D_73))) | ~m1_subset_1(E_74, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.33  tff(c_194, plain, (![A_75, B_76, E_77]: (k4_relset_1(A_75, B_76, '#skF_1', '#skF_2', E_77, '#skF_3')=k5_relat_1(E_77, '#skF_3') | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_32, c_187])).
% 2.59/1.33  tff(c_201, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_194])).
% 2.59/1.33  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.59/1.33  tff(c_58, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.59/1.33  tff(c_214, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_58])).
% 2.59/1.33  tff(c_226, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_214])).
% 2.59/1.33  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_181, c_73, c_226])).
% 2.59/1.33  tff(c_230, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.59/1.33  tff(c_402, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_230])).
% 2.59/1.33  tff(c_414, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_402])).
% 2.59/1.33  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_359, c_339, c_414])).
% 2.59/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  Inference rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Ref     : 0
% 2.59/1.33  #Sup     : 85
% 2.59/1.33  #Fact    : 0
% 2.59/1.33  #Define  : 0
% 2.59/1.33  #Split   : 1
% 2.59/1.33  #Chain   : 0
% 2.59/1.33  #Close   : 0
% 2.59/1.33  
% 2.59/1.33  Ordering : KBO
% 2.59/1.33  
% 2.59/1.33  Simplification rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Subsume      : 0
% 2.59/1.33  #Demod        : 36
% 2.59/1.33  #Tautology    : 43
% 2.59/1.33  #SimpNegUnit  : 0
% 2.59/1.33  #BackRed      : 3
% 2.59/1.33  
% 2.59/1.33  #Partial instantiations: 0
% 2.59/1.33  #Strategies tried      : 1
% 2.59/1.33  
% 2.59/1.33  Timing (in seconds)
% 2.59/1.33  ----------------------
% 2.59/1.33  Preprocessing        : 0.31
% 2.59/1.33  Parsing              : 0.17
% 2.59/1.33  CNF conversion       : 0.02
% 2.59/1.33  Main loop            : 0.25
% 2.59/1.33  Inferencing          : 0.11
% 2.59/1.33  Reduction            : 0.07
% 2.59/1.33  Demodulation         : 0.05
% 2.59/1.33  BG Simplification    : 0.01
% 2.59/1.33  Subsumption          : 0.03
% 2.59/1.33  Abstraction          : 0.02
% 2.59/1.33  MUC search           : 0.00
% 2.59/1.33  Cooper               : 0.00
% 2.59/1.33  Total                : 0.60
% 2.59/1.33  Index Insertion      : 0.00
% 2.59/1.33  Index Deletion       : 0.00
% 2.59/1.34  Index Matching       : 0.00
% 2.59/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
