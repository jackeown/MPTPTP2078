%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:46 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 112 expanded)
%              Number of leaves         :   34 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 179 expanded)
%              Number of equality atoms :   23 (  27 expanded)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_59,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_67,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_316,plain,(
    ! [A_98,B_99,D_100] :
      ( r2_relset_1(A_98,B_99,D_100,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_322,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_316])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_354,plain,(
    ! [B_105,A_106] :
      ( k5_relat_1(B_105,k6_partfun1(A_106)) = B_105
      | ~ r1_tarski(k2_relat_1(B_105),A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_358,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_354])).

tff(c_28,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_418,plain,(
    ! [C_115,A_116,F_118,D_119,E_120,B_117] :
      ( k4_relset_1(A_116,B_117,C_115,D_119,E_120,F_118) = k5_relat_1(E_120,F_118)
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_115,D_119)))
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_434,plain,(
    ! [A_124,B_125,A_126,E_127] :
      ( k4_relset_1(A_124,B_125,A_126,A_126,E_127,k6_partfun1(A_126)) = k5_relat_1(E_127,k6_partfun1(A_126))
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(resolution,[status(thm)],[c_28,c_418])).

tff(c_440,plain,(
    ! [A_126] : k4_relset_1('#skF_1','#skF_2',A_126,A_126,'#skF_3',k6_partfun1(A_126)) = k5_relat_1('#skF_3',k6_partfun1(A_126)) ),
    inference(resolution,[status(thm)],[c_34,c_434])).

tff(c_144,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_150,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_144])).

tff(c_71,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_86,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_86])).

tff(c_98,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_92])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_106,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_102])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [A_54,B_55] :
      ( k5_relat_1(k6_partfun1(A_54),B_55) = B_55
      | ~ r1_tarski(k1_relat_1(B_55),A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_129,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_123])).

tff(c_138,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_129])).

tff(c_220,plain,(
    ! [F_74,B_73,E_76,A_72,D_75,C_71] :
      ( k4_relset_1(A_72,B_73,C_71,D_75,E_76,F_74) = k5_relat_1(E_76,F_74)
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_71,D_75)))
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_227,plain,(
    ! [A_77,B_78,E_79] :
      ( k4_relset_1(A_77,B_78,'#skF_1','#skF_2',E_79,'#skF_3') = k5_relat_1(E_79,'#skF_3')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(resolution,[status(thm)],[c_34,c_220])).

tff(c_234,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_227])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_256,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_68])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_138,c_256])).

tff(c_260,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_445,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_260])).

tff(c_457,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_445])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_67,c_322,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.37  
% 2.49/1.37  %Foreground sorts:
% 2.49/1.37  
% 2.49/1.37  
% 2.49/1.37  %Background operators:
% 2.49/1.37  
% 2.49/1.37  
% 2.49/1.37  %Foreground operators:
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.49/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.37  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.49/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.37  
% 2.65/1.39  tff(f_90, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.65/1.39  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.65/1.39  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.65/1.39  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.65/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.65/1.39  tff(f_83, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.65/1.39  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.65/1.39  tff(f_81, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.65/1.39  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.65/1.39  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.65/1.39  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.65/1.39  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.65/1.39  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.65/1.39  tff(c_48, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.39  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_48])).
% 2.65/1.39  tff(c_59, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.39  tff(c_67, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.65/1.39  tff(c_316, plain, (![A_98, B_99, D_100]: (r2_relset_1(A_98, B_99, D_100, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.39  tff(c_322, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_316])).
% 2.65/1.39  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.39  tff(c_30, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.39  tff(c_10, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.39  tff(c_354, plain, (![B_105, A_106]: (k5_relat_1(B_105, k6_partfun1(A_106))=B_105 | ~r1_tarski(k2_relat_1(B_105), A_106) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.65/1.39  tff(c_358, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_354])).
% 2.65/1.39  tff(c_28, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.39  tff(c_418, plain, (![C_115, A_116, F_118, D_119, E_120, B_117]: (k4_relset_1(A_116, B_117, C_115, D_119, E_120, F_118)=k5_relat_1(E_120, F_118) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_115, D_119))) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.39  tff(c_434, plain, (![A_124, B_125, A_126, E_127]: (k4_relset_1(A_124, B_125, A_126, A_126, E_127, k6_partfun1(A_126))=k5_relat_1(E_127, k6_partfun1(A_126)) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(resolution, [status(thm)], [c_28, c_418])).
% 2.65/1.39  tff(c_440, plain, (![A_126]: (k4_relset_1('#skF_1', '#skF_2', A_126, A_126, '#skF_3', k6_partfun1(A_126))=k5_relat_1('#skF_3', k6_partfun1(A_126)))), inference(resolution, [status(thm)], [c_34, c_434])).
% 2.65/1.39  tff(c_144, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.39  tff(c_150, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_144])).
% 2.65/1.39  tff(c_71, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.39  tff(c_79, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.65/1.39  tff(c_86, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.39  tff(c_92, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_86])).
% 2.65/1.39  tff(c_98, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_92])).
% 2.65/1.39  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.39  tff(c_102, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 2.65/1.39  tff(c_106, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_102])).
% 2.65/1.39  tff(c_8, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.39  tff(c_123, plain, (![A_54, B_55]: (k5_relat_1(k6_partfun1(A_54), B_55)=B_55 | ~r1_tarski(k1_relat_1(B_55), A_54) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 2.65/1.39  tff(c_129, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_123])).
% 2.65/1.39  tff(c_138, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_129])).
% 2.65/1.39  tff(c_220, plain, (![F_74, B_73, E_76, A_72, D_75, C_71]: (k4_relset_1(A_72, B_73, C_71, D_75, E_76, F_74)=k5_relat_1(E_76, F_74) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_71, D_75))) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.39  tff(c_227, plain, (![A_77, B_78, E_79]: (k4_relset_1(A_77, B_78, '#skF_1', '#skF_2', E_79, '#skF_3')=k5_relat_1(E_79, '#skF_3') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(resolution, [status(thm)], [c_34, c_220])).
% 2.65/1.39  tff(c_234, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_227])).
% 2.65/1.39  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.65/1.39  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.65/1.39  tff(c_256, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_68])).
% 2.65/1.39  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_138, c_256])).
% 2.65/1.39  tff(c_260, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.65/1.39  tff(c_445, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_260])).
% 2.65/1.39  tff(c_457, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_358, c_445])).
% 2.65/1.39  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_67, c_322, c_457])).
% 2.65/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  Inference rules
% 2.65/1.39  ----------------------
% 2.65/1.39  #Ref     : 0
% 2.65/1.39  #Sup     : 90
% 2.65/1.39  #Fact    : 0
% 2.65/1.39  #Define  : 0
% 2.65/1.39  #Split   : 1
% 2.65/1.39  #Chain   : 0
% 2.65/1.39  #Close   : 0
% 2.65/1.39  
% 2.65/1.39  Ordering : KBO
% 2.65/1.39  
% 2.65/1.39  Simplification rules
% 2.65/1.39  ----------------------
% 2.65/1.39  #Subsume      : 0
% 2.65/1.39  #Demod        : 54
% 2.65/1.39  #Tautology    : 48
% 2.65/1.39  #SimpNegUnit  : 0
% 2.65/1.39  #BackRed      : 2
% 2.65/1.39  
% 2.65/1.39  #Partial instantiations: 0
% 2.65/1.39  #Strategies tried      : 1
% 2.65/1.39  
% 2.65/1.39  Timing (in seconds)
% 2.65/1.39  ----------------------
% 2.65/1.39  Preprocessing        : 0.31
% 2.65/1.39  Parsing              : 0.17
% 2.65/1.39  CNF conversion       : 0.02
% 2.65/1.39  Main loop            : 0.25
% 2.65/1.39  Inferencing          : 0.10
% 2.65/1.39  Reduction            : 0.08
% 2.65/1.39  Demodulation         : 0.06
% 2.65/1.39  BG Simplification    : 0.01
% 2.65/1.39  Subsumption          : 0.03
% 2.65/1.39  Abstraction          : 0.02
% 2.65/1.39  MUC search           : 0.00
% 2.65/1.39  Cooper               : 0.00
% 2.65/1.39  Total                : 0.60
% 2.65/1.39  Index Insertion      : 0.00
% 2.65/1.39  Index Deletion       : 0.00
% 2.65/1.39  Index Matching       : 0.00
% 2.65/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
