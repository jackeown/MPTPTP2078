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
% DateTime   : Thu Dec  3 10:11:50 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 129 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 207 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_86,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_49,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_273,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_281,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_273])).

tff(c_350,plain,(
    ! [A_103,B_104,D_105] :
      ( r2_relset_1(A_103,B_104,D_105,D_105)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_356,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_350])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_385,plain,(
    ! [B_112,A_113] :
      ( k5_relat_1(B_112,k6_partfun1(A_113)) = B_112
      | ~ r1_tarski(k2_relat_1(B_112),A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14])).

tff(c_389,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_385])).

tff(c_28,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_35,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_431,plain,(
    ! [E_119,A_121,D_123,B_120,F_122,C_118] :
      ( k4_relset_1(A_121,B_120,C_118,D_123,E_119,F_122) = k5_relat_1(E_119,F_122)
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_118,D_123)))
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_447,plain,(
    ! [A_127,B_128,A_129,E_130] :
      ( k4_relset_1(A_127,B_128,A_129,A_129,E_130,k6_partfun1(A_129)) = k5_relat_1(E_130,k6_partfun1(A_129))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(resolution,[status(thm)],[c_35,c_431])).

tff(c_453,plain,(
    ! [A_129] : k4_relset_1('#skF_1','#skF_2',A_129,A_129,'#skF_3',k6_partfun1(A_129)) = k5_relat_1('#skF_3',k6_partfun1(A_129)) ),
    inference(resolution,[status(thm)],[c_34,c_447])).

tff(c_128,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_67,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_75,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_10])).

tff(c_81,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_78])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_96,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_92])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [A_64,B_65] :
      ( k5_relat_1(k6_partfun1(A_64),B_65) = B_65
      | ~ r1_tarski(k1_relat_1(B_65),A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_156,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_150])).

tff(c_165,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_156])).

tff(c_225,plain,(
    ! [A_76,B_75,C_73,D_78,E_74,F_77] :
      ( k4_relset_1(A_76,B_75,C_73,D_78,E_74,F_77) = k5_relat_1(E_74,F_77)
      | ~ m1_subset_1(F_77,k1_zfmisc_1(k2_zfmisc_1(C_73,D_78)))
      | ~ m1_subset_1(E_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_232,plain,(
    ! [A_79,B_80,E_81] :
      ( k4_relset_1(A_79,B_80,'#skF_1','#skF_2',E_81,'#skF_3') = k5_relat_1(E_81,'#skF_3')
      | ~ m1_subset_1(E_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(resolution,[status(thm)],[c_34,c_225])).

tff(c_239,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_232])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_65,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_261,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_65])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_165,c_261])).

tff(c_265,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_458,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_265])).

tff(c_470,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_458])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_281,c_356,c_470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 10:11:22 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.38  
% 2.53/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.38  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.38  
% 2.53/1.38  %Foreground sorts:
% 2.53/1.38  
% 2.53/1.38  
% 2.53/1.38  %Background operators:
% 2.53/1.38  
% 2.53/1.38  
% 2.53/1.38  %Foreground operators:
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.53/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.53/1.38  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.53/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.38  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.53/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.38  
% 2.53/1.40  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.53/1.40  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.53/1.40  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.53/1.40  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.53/1.40  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.53/1.40  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.53/1.40  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.53/1.40  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.53/1.40  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.53/1.40  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.53/1.40  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.53/1.40  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.53/1.40  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.53/1.40  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.40  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.40  tff(c_49, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.40  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.53/1.40  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 2.53/1.40  tff(c_273, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.40  tff(c_281, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_273])).
% 2.53/1.40  tff(c_350, plain, (![A_103, B_104, D_105]: (r2_relset_1(A_103, B_104, D_105, D_105) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.53/1.40  tff(c_356, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_350])).
% 2.53/1.40  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.40  tff(c_30, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.40  tff(c_14, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.53/1.40  tff(c_385, plain, (![B_112, A_113]: (k5_relat_1(B_112, k6_partfun1(A_113))=B_112 | ~r1_tarski(k2_relat_1(B_112), A_113) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14])).
% 2.53/1.40  tff(c_389, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_385])).
% 2.53/1.40  tff(c_28, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.40  tff(c_35, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 2.53/1.40  tff(c_431, plain, (![E_119, A_121, D_123, B_120, F_122, C_118]: (k4_relset_1(A_121, B_120, C_118, D_123, E_119, F_122)=k5_relat_1(E_119, F_122) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_118, D_123))) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.53/1.40  tff(c_447, plain, (![A_127, B_128, A_129, E_130]: (k4_relset_1(A_127, B_128, A_129, A_129, E_130, k6_partfun1(A_129))=k5_relat_1(E_130, k6_partfun1(A_129)) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(resolution, [status(thm)], [c_35, c_431])).
% 2.53/1.40  tff(c_453, plain, (![A_129]: (k4_relset_1('#skF_1', '#skF_2', A_129, A_129, '#skF_3', k6_partfun1(A_129))=k5_relat_1('#skF_3', k6_partfun1(A_129)))), inference(resolution, [status(thm)], [c_34, c_447])).
% 2.53/1.40  tff(c_128, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.53/1.40  tff(c_134, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_128])).
% 2.53/1.40  tff(c_67, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.40  tff(c_75, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.53/1.40  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.40  tff(c_78, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_10])).
% 2.53/1.40  tff(c_81, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_78])).
% 2.53/1.40  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.40  tff(c_92, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_81, c_16])).
% 2.53/1.40  tff(c_96, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_92])).
% 2.53/1.40  tff(c_12, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.40  tff(c_150, plain, (![A_64, B_65]: (k5_relat_1(k6_partfun1(A_64), B_65)=B_65 | ~r1_tarski(k1_relat_1(B_65), A_64) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.53/1.40  tff(c_156, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_150])).
% 2.53/1.40  tff(c_165, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_156])).
% 2.53/1.40  tff(c_225, plain, (![A_76, B_75, C_73, D_78, E_74, F_77]: (k4_relset_1(A_76, B_75, C_73, D_78, E_74, F_77)=k5_relat_1(E_74, F_77) | ~m1_subset_1(F_77, k1_zfmisc_1(k2_zfmisc_1(C_73, D_78))) | ~m1_subset_1(E_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.53/1.40  tff(c_232, plain, (![A_79, B_80, E_81]: (k4_relset_1(A_79, B_80, '#skF_1', '#skF_2', E_81, '#skF_3')=k5_relat_1(E_81, '#skF_3') | ~m1_subset_1(E_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(resolution, [status(thm)], [c_34, c_225])).
% 2.53/1.40  tff(c_239, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_35, c_232])).
% 2.53/1.40  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.40  tff(c_65, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.53/1.40  tff(c_261, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_65])).
% 2.53/1.40  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_165, c_261])).
% 2.53/1.40  tff(c_265, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.53/1.40  tff(c_458, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_453, c_265])).
% 2.53/1.40  tff(c_470, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_389, c_458])).
% 2.53/1.40  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_281, c_356, c_470])).
% 2.53/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.40  
% 2.53/1.40  Inference rules
% 2.53/1.40  ----------------------
% 2.53/1.40  #Ref     : 0
% 2.53/1.40  #Sup     : 92
% 2.53/1.40  #Fact    : 0
% 2.53/1.40  #Define  : 0
% 2.53/1.40  #Split   : 1
% 2.53/1.40  #Chain   : 0
% 2.53/1.40  #Close   : 0
% 2.53/1.40  
% 2.53/1.40  Ordering : KBO
% 2.53/1.40  
% 2.53/1.40  Simplification rules
% 2.53/1.40  ----------------------
% 2.53/1.40  #Subsume      : 0
% 2.53/1.40  #Demod        : 57
% 2.53/1.40  #Tautology    : 48
% 2.53/1.40  #SimpNegUnit  : 0
% 2.53/1.40  #BackRed      : 2
% 2.53/1.40  
% 2.53/1.40  #Partial instantiations: 0
% 2.53/1.40  #Strategies tried      : 1
% 2.53/1.40  
% 2.53/1.40  Timing (in seconds)
% 2.53/1.40  ----------------------
% 2.53/1.40  Preprocessing        : 0.34
% 2.53/1.40  Parsing              : 0.18
% 2.53/1.40  CNF conversion       : 0.02
% 2.53/1.40  Main loop            : 0.26
% 2.53/1.40  Inferencing          : 0.11
% 2.53/1.40  Reduction            : 0.08
% 2.53/1.40  Demodulation         : 0.06
% 2.53/1.40  BG Simplification    : 0.02
% 2.53/1.40  Subsumption          : 0.03
% 2.53/1.40  Abstraction          : 0.02
% 2.53/1.40  MUC search           : 0.00
% 2.53/1.40  Cooper               : 0.00
% 2.53/1.40  Total                : 0.64
% 2.53/1.41  Index Insertion      : 0.00
% 2.53/1.41  Index Deletion       : 0.00
% 2.53/1.41  Index Matching       : 0.00
% 2.53/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
