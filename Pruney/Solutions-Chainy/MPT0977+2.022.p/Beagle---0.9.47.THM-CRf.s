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
% DateTime   : Thu Dec  3 10:11:48 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 107 expanded)
%              Number of leaves         :   33 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 178 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_55])).

tff(c_215,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_223,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_215])).

tff(c_284,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_relset_1(A_109,B_110,C_111,C_111)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    ! [C_122] :
      ( r2_relset_1('#skF_1','#skF_2',C_122,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_284])).

tff(c_306,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_303])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,(
    ! [B_99,A_100] :
      ( k5_relat_1(B_99,k6_partfun1(A_100)) = B_99
      | ~ r1_tarski(k2_relat_1(B_99),A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_240,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_partfun1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_236])).

tff(c_28,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_291,plain,(
    ! [B_115,F_116,D_117,E_118,A_114,C_113] :
      ( k4_relset_1(A_114,B_115,C_113,D_117,E_118,F_116) = k5_relat_1(E_118,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_113,D_117)))
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_335,plain,(
    ! [A_127,B_128,A_129,E_130] :
      ( k4_relset_1(A_127,B_128,A_129,A_129,E_130,k6_partfun1(A_129)) = k5_relat_1(E_130,k6_partfun1(A_129))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(resolution,[status(thm)],[c_28,c_291])).

tff(c_341,plain,(
    ! [A_129] : k4_relset_1('#skF_1','#skF_2',A_129,A_129,'#skF_3',k6_partfun1(A_129)) = k5_relat_1('#skF_3',k6_partfun1(A_129)) ),
    inference(resolution,[status(thm)],[c_34,c_335])).

tff(c_65,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_144,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( r2_relset_1(A_63,B_64,C_65,C_65)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_156,plain,(
    ! [C_70] :
      ( r2_relset_1('#skF_1','#skF_2',C_70,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_144])).

tff(c_159,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_156])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,(
    ! [A_53,B_54] :
      ( k5_relat_1(k6_partfun1(A_53),B_54) = B_54
      | ~ r1_tarski(k1_relat_1(B_54),A_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14])).

tff(c_100,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_160,plain,(
    ! [F_74,B_73,E_76,A_72,D_75,C_71] :
      ( k4_relset_1(A_72,B_73,C_71,D_75,E_76,F_74) = k5_relat_1(E_76,F_74)
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_71,D_75)))
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_167,plain,(
    ! [A_77,B_78,E_79] :
      ( k4_relset_1(A_77,B_78,'#skF_1','#skF_2',E_79,'#skF_3') = k5_relat_1(E_79,'#skF_3')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(resolution,[status(thm)],[c_34,c_160])).

tff(c_174,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_167])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_180,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_64])).

tff(c_199,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_180])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_73,c_159,c_199])).

tff(c_203,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_342,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_203])).

tff(c_354,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_342])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_223,c_306,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:51:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.32/1.34  
% 2.32/1.34  %Foreground sorts:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Background operators:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Foreground operators:
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.32/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.32/1.34  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.32/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.32/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.34  
% 2.32/1.36  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.36  tff(f_89, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.32/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.32/1.36  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.32/1.36  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.32/1.36  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.32/1.36  tff(f_82, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.32/1.36  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.32/1.36  tff(f_80, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.32/1.36  tff(f_70, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.32/1.36  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.32/1.36  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.32/1.36  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.36  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.32/1.36  tff(c_49, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.32/1.36  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.32/1.36  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_55])).
% 2.32/1.36  tff(c_215, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.36  tff(c_223, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_215])).
% 2.32/1.36  tff(c_284, plain, (![A_109, B_110, C_111, D_112]: (r2_relset_1(A_109, B_110, C_111, C_111) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.32/1.36  tff(c_303, plain, (![C_122]: (r2_relset_1('#skF_1', '#skF_2', C_122, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_284])).
% 2.32/1.36  tff(c_306, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_303])).
% 2.32/1.36  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.36  tff(c_30, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.36  tff(c_16, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.32/1.36  tff(c_236, plain, (![B_99, A_100]: (k5_relat_1(B_99, k6_partfun1(A_100))=B_99 | ~r1_tarski(k2_relat_1(B_99), A_100) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16])).
% 2.32/1.36  tff(c_240, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_partfun1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_236])).
% 2.32/1.36  tff(c_28, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.36  tff(c_291, plain, (![B_115, F_116, D_117, E_118, A_114, C_113]: (k4_relset_1(A_114, B_115, C_113, D_117, E_118, F_116)=k5_relat_1(E_118, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_113, D_117))) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.32/1.36  tff(c_335, plain, (![A_127, B_128, A_129, E_130]: (k4_relset_1(A_127, B_128, A_129, A_129, E_130, k6_partfun1(A_129))=k5_relat_1(E_130, k6_partfun1(A_129)) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(resolution, [status(thm)], [c_28, c_291])).
% 2.32/1.36  tff(c_341, plain, (![A_129]: (k4_relset_1('#skF_1', '#skF_2', A_129, A_129, '#skF_3', k6_partfun1(A_129))=k5_relat_1('#skF_3', k6_partfun1(A_129)))), inference(resolution, [status(thm)], [c_34, c_335])).
% 2.32/1.36  tff(c_65, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.36  tff(c_73, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.32/1.36  tff(c_144, plain, (![A_63, B_64, C_65, D_66]: (r2_relset_1(A_63, B_64, C_65, C_65) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.32/1.36  tff(c_156, plain, (![C_70]: (r2_relset_1('#skF_1', '#skF_2', C_70, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_144])).
% 2.32/1.36  tff(c_159, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_156])).
% 2.32/1.36  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.32/1.36  tff(c_14, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.36  tff(c_96, plain, (![A_53, B_54]: (k5_relat_1(k6_partfun1(A_53), B_54)=B_54 | ~r1_tarski(k1_relat_1(B_54), A_53) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14])).
% 2.32/1.36  tff(c_100, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.32/1.36  tff(c_160, plain, (![F_74, B_73, E_76, A_72, D_75, C_71]: (k4_relset_1(A_72, B_73, C_71, D_75, E_76, F_74)=k5_relat_1(E_76, F_74) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_71, D_75))) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.32/1.36  tff(c_167, plain, (![A_77, B_78, E_79]: (k4_relset_1(A_77, B_78, '#skF_1', '#skF_2', E_79, '#skF_3')=k5_relat_1(E_79, '#skF_3') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(resolution, [status(thm)], [c_34, c_160])).
% 2.32/1.36  tff(c_174, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_167])).
% 2.32/1.36  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.32/1.36  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.32/1.36  tff(c_180, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_64])).
% 2.32/1.36  tff(c_199, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_180])).
% 2.32/1.36  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_73, c_159, c_199])).
% 2.32/1.36  tff(c_203, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.32/1.36  tff(c_342, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_203])).
% 2.32/1.36  tff(c_354, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_240, c_342])).
% 2.32/1.36  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_223, c_306, c_354])).
% 2.32/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.36  
% 2.32/1.36  Inference rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Ref     : 0
% 2.32/1.36  #Sup     : 67
% 2.32/1.36  #Fact    : 0
% 2.32/1.36  #Define  : 0
% 2.32/1.36  #Split   : 1
% 2.32/1.36  #Chain   : 0
% 2.32/1.36  #Close   : 0
% 2.32/1.36  
% 2.32/1.36  Ordering : KBO
% 2.32/1.36  
% 2.32/1.36  Simplification rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Subsume      : 2
% 2.32/1.36  #Demod        : 26
% 2.32/1.36  #Tautology    : 27
% 2.32/1.36  #SimpNegUnit  : 0
% 2.32/1.36  #BackRed      : 3
% 2.32/1.36  
% 2.32/1.36  #Partial instantiations: 0
% 2.32/1.36  #Strategies tried      : 1
% 2.32/1.36  
% 2.32/1.36  Timing (in seconds)
% 2.32/1.36  ----------------------
% 2.32/1.36  Preprocessing        : 0.33
% 2.32/1.36  Parsing              : 0.19
% 2.32/1.36  CNF conversion       : 0.02
% 2.32/1.36  Main loop            : 0.24
% 2.32/1.36  Inferencing          : 0.10
% 2.32/1.36  Reduction            : 0.07
% 2.32/1.36  Demodulation         : 0.05
% 2.32/1.36  BG Simplification    : 0.01
% 2.32/1.36  Subsumption          : 0.03
% 2.32/1.36  Abstraction          : 0.01
% 2.32/1.36  MUC search           : 0.00
% 2.32/1.36  Cooper               : 0.00
% 2.32/1.36  Total                : 0.60
% 2.32/1.36  Index Insertion      : 0.00
% 2.32/1.36  Index Deletion       : 0.00
% 2.32/1.36  Index Matching       : 0.00
% 2.32/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
