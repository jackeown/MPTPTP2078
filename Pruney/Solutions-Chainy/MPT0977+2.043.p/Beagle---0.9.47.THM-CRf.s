%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 121 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 193 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_45,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_57,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_248,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_256,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_248])).

tff(c_290,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( r2_relset_1(A_96,B_97,C_98,C_98)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_302,plain,(
    ! [C_103] :
      ( r2_relset_1('#skF_1','#skF_2',C_103,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_290])).

tff(c_305,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_302])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_257,plain,(
    ! [B_89,A_90] :
      ( k5_relat_1(B_89,k6_partfun1(A_90)) = B_89
      | ~ r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_261,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_24,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_31,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_306,plain,(
    ! [C_104,D_108,A_105,F_107,E_109,B_106] :
      ( k4_relset_1(A_105,B_106,C_104,D_108,E_109,F_107) = k5_relat_1(E_109,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_104,D_108)))
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_341,plain,(
    ! [A_114,B_115,A_116,E_117] :
      ( k4_relset_1(A_114,B_115,A_116,A_116,E_117,k6_partfun1(A_116)) = k5_relat_1(E_117,k6_partfun1(A_116))
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(resolution,[status(thm)],[c_31,c_306])).

tff(c_347,plain,(
    ! [A_116] : k4_relset_1('#skF_1','#skF_2',A_116,A_116,'#skF_3',k6_partfun1(A_116)) = k5_relat_1('#skF_3',k6_partfun1(A_116)) ),
    inference(resolution,[status(thm)],[c_30,c_341])).

tff(c_153,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( r2_relset_1(A_59,B_60,C_61,C_61)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_165,plain,(
    ! [C_66] :
      ( r2_relset_1('#skF_1','#skF_2',C_66,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_153])).

tff(c_168,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_76,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_76])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_10])).

tff(c_90,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_87])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_partfun1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_169,plain,(
    ! [E_72,F_70,C_67,B_69,D_71,A_68] :
      ( k4_relset_1(A_68,B_69,C_67,D_71,E_72,F_70) = k5_relat_1(E_72,F_70)
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_67,D_71)))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_176,plain,(
    ! [A_73,B_74,E_75] :
      ( k4_relset_1(A_73,B_74,'#skF_1','#skF_2',E_75,'#skF_3') = k5_relat_1(E_75,'#skF_3')
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_30,c_169])).

tff(c_183,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_31,c_176])).

tff(c_28,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_69,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_189,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_69])).

tff(c_201,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_189])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_168,c_90,c_201])).

tff(c_205,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_348,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_205])).

tff(c_360,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_348])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_256,c_305,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.31  
% 2.41/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.41/1.31  
% 2.41/1.31  %Foreground sorts:
% 2.41/1.31  
% 2.41/1.31  
% 2.41/1.31  %Background operators:
% 2.41/1.31  
% 2.41/1.31  
% 2.41/1.31  %Foreground operators:
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.41/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.41/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.41/1.31  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.41/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.41/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.41/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.31  
% 2.41/1.33  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.41/1.33  tff(f_85, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.41/1.33  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.41/1.33  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.41/1.33  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.41/1.33  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.41/1.33  tff(f_78, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.41/1.33  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.41/1.33  tff(f_76, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.41/1.33  tff(f_68, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.41/1.33  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.41/1.33  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.41/1.33  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.33  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.33  tff(c_45, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.41/1.33  tff(c_51, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.41/1.33  tff(c_57, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 2.41/1.33  tff(c_248, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.33  tff(c_256, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_248])).
% 2.41/1.33  tff(c_290, plain, (![A_96, B_97, C_98, D_99]: (r2_relset_1(A_96, B_97, C_98, C_98) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.41/1.33  tff(c_302, plain, (![C_103]: (r2_relset_1('#skF_1', '#skF_2', C_103, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_290])).
% 2.41/1.33  tff(c_305, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_302])).
% 2.41/1.33  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.41/1.33  tff(c_26, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.41/1.33  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.33  tff(c_257, plain, (![B_89, A_90]: (k5_relat_1(B_89, k6_partfun1(A_90))=B_89 | ~r1_tarski(k2_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 2.41/1.33  tff(c_261, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_257])).
% 2.41/1.33  tff(c_24, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.33  tff(c_31, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 2.41/1.33  tff(c_306, plain, (![C_104, D_108, A_105, F_107, E_109, B_106]: (k4_relset_1(A_105, B_106, C_104, D_108, E_109, F_107)=k5_relat_1(E_109, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_104, D_108))) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.33  tff(c_341, plain, (![A_114, B_115, A_116, E_117]: (k4_relset_1(A_114, B_115, A_116, A_116, E_117, k6_partfun1(A_116))=k5_relat_1(E_117, k6_partfun1(A_116)) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(resolution, [status(thm)], [c_31, c_306])).
% 2.41/1.33  tff(c_347, plain, (![A_116]: (k4_relset_1('#skF_1', '#skF_2', A_116, A_116, '#skF_3', k6_partfun1(A_116))=k5_relat_1('#skF_3', k6_partfun1(A_116)))), inference(resolution, [status(thm)], [c_30, c_341])).
% 2.41/1.33  tff(c_153, plain, (![A_59, B_60, C_61, D_62]: (r2_relset_1(A_59, B_60, C_61, C_61) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.41/1.33  tff(c_165, plain, (![C_66]: (r2_relset_1('#skF_1', '#skF_2', C_66, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_153])).
% 2.41/1.33  tff(c_168, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_165])).
% 2.41/1.33  tff(c_76, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.33  tff(c_84, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_76])).
% 2.41/1.33  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.33  tff(c_87, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_10])).
% 2.41/1.33  tff(c_90, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_87])).
% 2.41/1.33  tff(c_14, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.41/1.33  tff(c_32, plain, (![A_12, B_13]: (k5_relat_1(k6_partfun1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 2.41/1.33  tff(c_169, plain, (![E_72, F_70, C_67, B_69, D_71, A_68]: (k4_relset_1(A_68, B_69, C_67, D_71, E_72, F_70)=k5_relat_1(E_72, F_70) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_67, D_71))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.33  tff(c_176, plain, (![A_73, B_74, E_75]: (k4_relset_1(A_73, B_74, '#skF_1', '#skF_2', E_75, '#skF_3')=k5_relat_1(E_75, '#skF_3') | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_30, c_169])).
% 2.41/1.33  tff(c_183, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_31, c_176])).
% 2.41/1.33  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.33  tff(c_69, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.41/1.33  tff(c_189, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_69])).
% 2.41/1.33  tff(c_201, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_189])).
% 2.41/1.33  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_168, c_90, c_201])).
% 2.41/1.33  tff(c_205, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.41/1.33  tff(c_348, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_205])).
% 2.41/1.33  tff(c_360, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_348])).
% 2.41/1.33  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_256, c_305, c_360])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 71
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 1
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 2
% 2.41/1.33  #Demod        : 31
% 2.41/1.33  #Tautology    : 31
% 2.41/1.33  #SimpNegUnit  : 0
% 2.41/1.33  #BackRed      : 3
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.33  Preprocessing        : 0.30
% 2.41/1.33  Parsing              : 0.16
% 2.41/1.33  CNF conversion       : 0.02
% 2.41/1.33  Main loop            : 0.23
% 2.41/1.33  Inferencing          : 0.10
% 2.41/1.33  Reduction            : 0.07
% 2.41/1.33  Demodulation         : 0.05
% 2.41/1.33  BG Simplification    : 0.01
% 2.41/1.33  Subsumption          : 0.03
% 2.41/1.33  Abstraction          : 0.01
% 2.41/1.33  MUC search           : 0.00
% 2.41/1.33  Cooper               : 0.00
% 2.41/1.33  Total                : 0.56
% 2.41/1.33  Index Insertion      : 0.00
% 2.41/1.33  Index Deletion       : 0.00
% 2.41/1.33  Index Matching       : 0.00
% 2.41/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
