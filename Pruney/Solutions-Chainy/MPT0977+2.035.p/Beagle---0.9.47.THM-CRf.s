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
% DateTime   : Thu Dec  3 10:11:50 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 130 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 215 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_80,axiom,(
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
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

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
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_256,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_264,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_256])).

tff(c_366,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( r2_relset_1(A_106,B_107,C_108,C_108)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_378,plain,(
    ! [C_113] :
      ( r2_relset_1('#skF_1','#skF_2',C_113,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_366])).

tff(c_381,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_378])).

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

tff(c_309,plain,(
    ! [B_99,A_100] :
      ( k5_relat_1(B_99,k6_partfun1(A_100)) = B_99
      | ~ r1_tarski(k2_relat_1(B_99),A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14])).

tff(c_313,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_309])).

tff(c_28,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_401,plain,(
    ! [B_118,A_119,F_120,D_121,E_117,C_116] :
      ( k4_relset_1(A_119,B_118,C_116,D_121,E_117,F_120) = k5_relat_1(E_117,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_116,D_121)))
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_432,plain,(
    ! [A_126,B_127,A_128,E_129] :
      ( k4_relset_1(A_126,B_127,A_128,A_128,E_129,k6_partfun1(A_128)) = k5_relat_1(E_129,k6_partfun1(A_128))
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(resolution,[status(thm)],[c_28,c_401])).

tff(c_438,plain,(
    ! [A_128] : k4_relset_1('#skF_1','#skF_2',A_128,A_128,'#skF_3',k6_partfun1(A_128)) = k5_relat_1('#skF_3',k6_partfun1(A_128)) ),
    inference(resolution,[status(thm)],[c_34,c_432])).

tff(c_185,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r2_relset_1(A_64,B_65,C_66,C_66)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_197,plain,(
    ! [C_71] :
      ( r2_relset_1('#skF_1','#skF_2',C_71,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_200,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_197])).

tff(c_65,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_85,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_85])).

tff(c_97,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_91])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_16])).

tff(c_106,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_102])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_partfun1(A_57),B_58) = B_58
      | ~ r1_tarski(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_134,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_128])).

tff(c_143,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_134])).

tff(c_220,plain,(
    ! [A_77,C_74,F_78,D_79,E_75,B_76] :
      ( k4_relset_1(A_77,B_76,C_74,D_79,E_75,F_78) = k5_relat_1(E_75,F_78)
      | ~ m1_subset_1(F_78,k1_zfmisc_1(k2_zfmisc_1(C_74,D_79)))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_227,plain,(
    ! [A_80,B_81,E_82] :
      ( k4_relset_1(A_80,B_81,'#skF_1','#skF_2',E_82,'#skF_3') = k5_relat_1(E_82,'#skF_3')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_34,c_220])).

tff(c_234,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_227])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_240,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_64])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_143,c_240])).

tff(c_244,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_439,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_244])).

tff(c_451,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_439])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_264,c_381,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.39  
% 2.54/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.40  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.54/1.40  
% 2.54/1.40  %Foreground sorts:
% 2.54/1.40  
% 2.54/1.40  
% 2.54/1.40  %Background operators:
% 2.54/1.40  
% 2.54/1.40  
% 2.54/1.40  %Foreground operators:
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.54/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.54/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.54/1.40  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.54/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.54/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.40  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.54/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.40  
% 2.54/1.41  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.54/1.41  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.54/1.41  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.54/1.41  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.54/1.41  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.54/1.41  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.54/1.41  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.54/1.41  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.54/1.41  tff(f_84, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.54/1.41  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.54/1.41  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.54/1.41  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.54/1.41  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.54/1.41  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.54/1.41  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.54/1.41  tff(c_49, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.41  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.54/1.41  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 2.54/1.41  tff(c_256, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.41  tff(c_264, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_256])).
% 2.54/1.41  tff(c_366, plain, (![A_106, B_107, C_108, D_109]: (r2_relset_1(A_106, B_107, C_108, C_108) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.41  tff(c_378, plain, (![C_113]: (r2_relset_1('#skF_1', '#skF_2', C_113, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_366])).
% 2.54/1.41  tff(c_381, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_378])).
% 2.54/1.41  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.41  tff(c_30, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.54/1.41  tff(c_14, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.54/1.41  tff(c_309, plain, (![B_99, A_100]: (k5_relat_1(B_99, k6_partfun1(A_100))=B_99 | ~r1_tarski(k2_relat_1(B_99), A_100) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14])).
% 2.54/1.41  tff(c_313, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_309])).
% 2.54/1.41  tff(c_28, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.54/1.41  tff(c_401, plain, (![B_118, A_119, F_120, D_121, E_117, C_116]: (k4_relset_1(A_119, B_118, C_116, D_121, E_117, F_120)=k5_relat_1(E_117, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_116, D_121))) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.54/1.41  tff(c_432, plain, (![A_126, B_127, A_128, E_129]: (k4_relset_1(A_126, B_127, A_128, A_128, E_129, k6_partfun1(A_128))=k5_relat_1(E_129, k6_partfun1(A_128)) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(resolution, [status(thm)], [c_28, c_401])).
% 2.54/1.41  tff(c_438, plain, (![A_128]: (k4_relset_1('#skF_1', '#skF_2', A_128, A_128, '#skF_3', k6_partfun1(A_128))=k5_relat_1('#skF_3', k6_partfun1(A_128)))), inference(resolution, [status(thm)], [c_34, c_432])).
% 2.54/1.41  tff(c_185, plain, (![A_64, B_65, C_66, D_67]: (r2_relset_1(A_64, B_65, C_66, C_66) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.41  tff(c_197, plain, (![C_71]: (r2_relset_1('#skF_1', '#skF_2', C_71, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_185])).
% 2.54/1.41  tff(c_200, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_197])).
% 2.54/1.41  tff(c_65, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.41  tff(c_73, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.54/1.41  tff(c_85, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.54/1.41  tff(c_91, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_73, c_85])).
% 2.54/1.41  tff(c_97, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_91])).
% 2.54/1.41  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.41  tff(c_102, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97, c_16])).
% 2.54/1.41  tff(c_106, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_102])).
% 2.54/1.41  tff(c_12, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.41  tff(c_128, plain, (![A_57, B_58]: (k5_relat_1(k6_partfun1(A_57), B_58)=B_58 | ~r1_tarski(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.54/1.41  tff(c_134, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_128])).
% 2.54/1.41  tff(c_143, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_134])).
% 2.54/1.41  tff(c_220, plain, (![A_77, C_74, F_78, D_79, E_75, B_76]: (k4_relset_1(A_77, B_76, C_74, D_79, E_75, F_78)=k5_relat_1(E_75, F_78) | ~m1_subset_1(F_78, k1_zfmisc_1(k2_zfmisc_1(C_74, D_79))) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.54/1.41  tff(c_227, plain, (![A_80, B_81, E_82]: (k4_relset_1(A_80, B_81, '#skF_1', '#skF_2', E_82, '#skF_3')=k5_relat_1(E_82, '#skF_3') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_34, c_220])).
% 2.54/1.41  tff(c_234, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_227])).
% 2.54/1.41  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.54/1.41  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.54/1.41  tff(c_240, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_64])).
% 2.54/1.41  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_143, c_240])).
% 2.54/1.41  tff(c_244, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.41  tff(c_439, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_244])).
% 2.54/1.41  tff(c_451, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_313, c_439])).
% 2.54/1.41  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_264, c_381, c_451])).
% 2.54/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.41  
% 2.54/1.41  Inference rules
% 2.54/1.41  ----------------------
% 2.54/1.41  #Ref     : 0
% 2.54/1.41  #Sup     : 89
% 2.54/1.41  #Fact    : 0
% 2.54/1.41  #Define  : 0
% 2.54/1.41  #Split   : 1
% 2.54/1.41  #Chain   : 0
% 2.54/1.41  #Close   : 0
% 2.54/1.41  
% 2.54/1.41  Ordering : KBO
% 2.54/1.41  
% 2.54/1.41  Simplification rules
% 2.54/1.41  ----------------------
% 2.54/1.41  #Subsume      : 0
% 2.54/1.41  #Demod        : 54
% 2.54/1.41  #Tautology    : 45
% 2.54/1.41  #SimpNegUnit  : 0
% 2.54/1.41  #BackRed      : 3
% 2.54/1.41  
% 2.54/1.41  #Partial instantiations: 0
% 2.54/1.41  #Strategies tried      : 1
% 2.54/1.41  
% 2.54/1.41  Timing (in seconds)
% 2.54/1.41  ----------------------
% 2.54/1.42  Preprocessing        : 0.33
% 2.54/1.42  Parsing              : 0.18
% 2.54/1.42  CNF conversion       : 0.02
% 2.54/1.42  Main loop            : 0.27
% 2.54/1.42  Inferencing          : 0.11
% 2.54/1.42  Reduction            : 0.08
% 2.54/1.42  Demodulation         : 0.06
% 2.54/1.42  BG Simplification    : 0.01
% 2.54/1.42  Subsumption          : 0.03
% 2.54/1.42  Abstraction          : 0.02
% 2.54/1.42  MUC search           : 0.00
% 2.54/1.42  Cooper               : 0.00
% 2.54/1.42  Total                : 0.63
% 2.54/1.42  Index Insertion      : 0.00
% 2.54/1.42  Index Deletion       : 0.00
% 2.54/1.42  Index Matching       : 0.00
% 2.54/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
