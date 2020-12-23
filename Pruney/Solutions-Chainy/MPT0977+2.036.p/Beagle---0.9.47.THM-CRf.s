%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:50 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 116 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 189 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_47,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_59,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_53])).

tff(c_217,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_225,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_300,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( r2_relset_1(A_102,B_103,C_104,C_104)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_319,plain,(
    ! [C_115] :
      ( r2_relset_1('#skF_1','#skF_2',C_115,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_300])).

tff(c_322,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_319])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_268,plain,(
    ! [B_96,A_97] :
      ( k5_relat_1(B_96,k6_partfun1(A_97)) = B_96
      | ~ r1_tarski(k2_relat_1(B_96),A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_272,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_26,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_307,plain,(
    ! [E_111,B_108,F_109,A_107,C_106,D_110] :
      ( k4_relset_1(A_107,B_108,C_106,D_110,E_111,F_109) = k5_relat_1(E_111,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_106,D_110)))
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_351,plain,(
    ! [A_120,B_121,A_122,E_123] :
      ( k4_relset_1(A_120,B_121,A_122,A_122,E_123,k6_partfun1(A_122)) = k5_relat_1(E_123,k6_partfun1(A_122))
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(resolution,[status(thm)],[c_26,c_307])).

tff(c_357,plain,(
    ! [A_122] : k4_relset_1('#skF_1','#skF_2',A_122,A_122,'#skF_3',k6_partfun1(A_122)) = k5_relat_1('#skF_3',k6_partfun1(A_122)) ),
    inference(resolution,[status(thm)],[c_32,c_351])).

tff(c_155,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( r2_relset_1(A_60,B_61,C_62,C_62)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_162,plain,(
    ! [C_64] :
      ( r2_relset_1('#skF_1','#skF_2',C_64,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_165,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_61,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_61])).

tff(c_97,plain,(
    ! [B_51,A_52] :
      ( k7_relat_1(B_51,A_52) = B_51
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_97])).

tff(c_109,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_103])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_33,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_partfun1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_166,plain,(
    ! [F_68,B_67,A_66,C_65,E_70,D_69] :
      ( k4_relset_1(A_66,B_67,C_65,D_69,E_70,F_68) = k5_relat_1(E_70,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_65,D_69)))
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_178,plain,(
    ! [A_74,B_75,E_76] :
      ( k4_relset_1(A_74,B_75,'#skF_1','#skF_2',E_76,'#skF_3') = k5_relat_1(E_76,'#skF_3')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(resolution,[status(thm)],[c_32,c_166])).

tff(c_185,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_178])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_191,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_70])).

tff(c_210,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_191])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_165,c_109,c_210])).

tff(c_214,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_358,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_214])).

tff(c_370,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_358])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_225,c_322,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.18/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.18/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.31  
% 2.57/1.33  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.57/1.33  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.57/1.33  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.57/1.33  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.57/1.33  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.57/1.33  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.57/1.33  tff(f_80, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.57/1.33  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.57/1.33  tff(f_78, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.57/1.33  tff(f_68, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.57/1.33  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.57/1.33  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.57/1.33  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.33  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.33  tff(c_47, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.33  tff(c_53, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.57/1.33  tff(c_59, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_53])).
% 2.57/1.33  tff(c_217, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.33  tff(c_225, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_217])).
% 2.57/1.33  tff(c_300, plain, (![A_102, B_103, C_104, D_105]: (r2_relset_1(A_102, B_103, C_104, C_104) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.57/1.33  tff(c_319, plain, (![C_115]: (r2_relset_1('#skF_1', '#skF_2', C_115, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_300])).
% 2.57/1.33  tff(c_322, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_319])).
% 2.57/1.33  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.33  tff(c_28, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.33  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.33  tff(c_268, plain, (![B_96, A_97]: (k5_relat_1(B_96, k6_partfun1(A_97))=B_96 | ~r1_tarski(k2_relat_1(B_96), A_97) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.57/1.33  tff(c_272, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.57/1.33  tff(c_26, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.57/1.33  tff(c_307, plain, (![E_111, B_108, F_109, A_107, C_106, D_110]: (k4_relset_1(A_107, B_108, C_106, D_110, E_111, F_109)=k5_relat_1(E_111, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_106, D_110))) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.33  tff(c_351, plain, (![A_120, B_121, A_122, E_123]: (k4_relset_1(A_120, B_121, A_122, A_122, E_123, k6_partfun1(A_122))=k5_relat_1(E_123, k6_partfun1(A_122)) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(resolution, [status(thm)], [c_26, c_307])).
% 2.57/1.33  tff(c_357, plain, (![A_122]: (k4_relset_1('#skF_1', '#skF_2', A_122, A_122, '#skF_3', k6_partfun1(A_122))=k5_relat_1('#skF_3', k6_partfun1(A_122)))), inference(resolution, [status(thm)], [c_32, c_351])).
% 2.57/1.33  tff(c_155, plain, (![A_60, B_61, C_62, D_63]: (r2_relset_1(A_60, B_61, C_62, C_62) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.57/1.33  tff(c_162, plain, (![C_64]: (r2_relset_1('#skF_1', '#skF_2', C_64, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_155])).
% 2.57/1.33  tff(c_165, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_162])).
% 2.57/1.33  tff(c_61, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.33  tff(c_69, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_61])).
% 2.57/1.33  tff(c_97, plain, (![B_51, A_52]: (k7_relat_1(B_51, A_52)=B_51 | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.33  tff(c_103, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_69, c_97])).
% 2.57/1.33  tff(c_109, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_103])).
% 2.57/1.33  tff(c_14, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.33  tff(c_33, plain, (![A_12, B_13]: (k5_relat_1(k6_partfun1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14])).
% 2.57/1.33  tff(c_166, plain, (![F_68, B_67, A_66, C_65, E_70, D_69]: (k4_relset_1(A_66, B_67, C_65, D_69, E_70, F_68)=k5_relat_1(E_70, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_65, D_69))) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.33  tff(c_178, plain, (![A_74, B_75, E_76]: (k4_relset_1(A_74, B_75, '#skF_1', '#skF_2', E_76, '#skF_3')=k5_relat_1(E_76, '#skF_3') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(resolution, [status(thm)], [c_32, c_166])).
% 2.57/1.33  tff(c_185, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_178])).
% 2.57/1.33  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.33  tff(c_70, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.57/1.33  tff(c_191, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_70])).
% 2.57/1.33  tff(c_210, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_191])).
% 2.57/1.33  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_165, c_109, c_210])).
% 2.57/1.33  tff(c_214, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.57/1.33  tff(c_358, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_214])).
% 2.57/1.33  tff(c_370, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_272, c_358])).
% 2.57/1.33  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_225, c_322, c_370])).
% 2.57/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  Inference rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Ref     : 0
% 2.57/1.33  #Sup     : 73
% 2.57/1.33  #Fact    : 0
% 2.57/1.33  #Define  : 0
% 2.57/1.33  #Split   : 1
% 2.57/1.33  #Chain   : 0
% 2.57/1.33  #Close   : 0
% 2.57/1.33  
% 2.57/1.33  Ordering : KBO
% 2.57/1.33  
% 2.57/1.33  Simplification rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Subsume      : 2
% 2.57/1.33  #Demod        : 30
% 2.57/1.33  #Tautology    : 33
% 2.57/1.33  #SimpNegUnit  : 0
% 2.57/1.33  #BackRed      : 3
% 2.57/1.33  
% 2.57/1.33  #Partial instantiations: 0
% 2.57/1.33  #Strategies tried      : 1
% 2.57/1.33  
% 2.57/1.33  Timing (in seconds)
% 2.57/1.33  ----------------------
% 2.57/1.33  Preprocessing        : 0.31
% 2.57/1.33  Parsing              : 0.17
% 2.57/1.33  CNF conversion       : 0.02
% 2.57/1.33  Main loop            : 0.25
% 2.57/1.33  Inferencing          : 0.10
% 2.57/1.33  Reduction            : 0.07
% 2.57/1.33  Demodulation         : 0.05
% 2.57/1.33  BG Simplification    : 0.01
% 2.57/1.33  Subsumption          : 0.03
% 2.57/1.33  Abstraction          : 0.01
% 2.57/1.33  MUC search           : 0.00
% 2.57/1.33  Cooper               : 0.00
% 2.57/1.33  Total                : 0.60
% 2.57/1.33  Index Insertion      : 0.00
% 2.57/1.33  Index Deletion       : 0.00
% 2.57/1.33  Index Matching       : 0.00
% 2.57/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
