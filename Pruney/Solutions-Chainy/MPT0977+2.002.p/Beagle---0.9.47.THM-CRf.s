%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   68 (  95 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :   98 ( 154 expanded)
%              Number of equality atoms :   18 (  22 expanded)
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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_79,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_198,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_198])).

tff(c_268,plain,(
    ! [A_98,B_99,D_100] :
      ( r2_relset_1(A_98,B_99,D_100,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_274,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_268])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_228,plain,(
    ! [B_90,A_91] :
      ( k5_relat_1(B_90,k6_partfun1(A_91)) = B_90
      | ~ r1_tarski(k2_relat_1(B_90),A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_232,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_228])).

tff(c_28,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_302,plain,(
    ! [A_113,D_109,C_108,B_110,E_112,F_111] :
      ( k4_relset_1(A_113,B_110,C_108,D_109,E_112,F_111) = k5_relat_1(E_112,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_108,D_109)))
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_373,plain,(
    ! [A_118,B_119,A_120,E_121] :
      ( k4_relset_1(A_118,B_119,A_120,A_120,E_121,k6_partfun1(A_120)) = k5_relat_1(E_121,k6_partfun1(A_120))
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(resolution,[status(thm)],[c_28,c_302])).

tff(c_379,plain,(
    ! [A_120] : k4_relset_1('#skF_1','#skF_2',A_120,A_120,'#skF_3',k6_partfun1(A_120)) = k5_relat_1('#skF_3',k6_partfun1(A_120)) ),
    inference(resolution,[status(thm)],[c_34,c_373])).

tff(c_81,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_131,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_relset_1(A_58,B_59,D_60,D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_54,B_55] :
      ( k5_relat_1(k6_partfun1(A_54),B_55) = B_55
      | ~ r1_tarski(k1_relat_1(B_55),A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_109,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_partfun1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_160,plain,(
    ! [E_72,B_70,F_71,C_68,A_73,D_69] :
      ( k4_relset_1(A_73,B_70,C_68,D_69,E_72,F_71) = k5_relat_1(E_72,F_71)
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(C_68,D_69)))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    ! [A_74,B_75,E_76] :
      ( k4_relset_1(A_74,B_75,'#skF_1','#skF_2',E_76,'#skF_3') = k5_relat_1(E_76,'#skF_3')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(resolution,[status(thm)],[c_34,c_160])).

tff(c_174,plain,(
    ! [A_25] : k4_relset_1(A_25,A_25,'#skF_1','#skF_2',k6_partfun1(A_25),'#skF_3') = k5_relat_1(k6_partfun1(A_25),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_167])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_180,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_60])).

tff(c_192,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_180])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_89,c_137,c_192])).

tff(c_196,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_380,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_196])).

tff(c_392,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_380])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_206,c_274,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:28:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.51/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.34  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.51/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.51/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.34  
% 2.60/1.36  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.60/1.36  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.60/1.36  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.60/1.36  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.60/1.36  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.60/1.36  tff(f_79, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.60/1.36  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.60/1.36  tff(f_77, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.60/1.36  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.60/1.36  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.60/1.36  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.60/1.36  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.60/1.36  tff(c_48, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.60/1.36  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_48])).
% 2.60/1.36  tff(c_198, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_206, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_198])).
% 2.60/1.36  tff(c_268, plain, (![A_98, B_99, D_100]: (r2_relset_1(A_98, B_99, D_100, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.60/1.36  tff(c_274, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_268])).
% 2.60/1.36  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.36  tff(c_30, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.60/1.36  tff(c_12, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.36  tff(c_228, plain, (![B_90, A_91]: (k5_relat_1(B_90, k6_partfun1(A_91))=B_90 | ~r1_tarski(k2_relat_1(B_90), A_91) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.60/1.36  tff(c_232, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_8, c_228])).
% 2.60/1.36  tff(c_28, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.36  tff(c_302, plain, (![A_113, D_109, C_108, B_110, E_112, F_111]: (k4_relset_1(A_113, B_110, C_108, D_109, E_112, F_111)=k5_relat_1(E_112, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_108, D_109))) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_110))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.36  tff(c_373, plain, (![A_118, B_119, A_120, E_121]: (k4_relset_1(A_118, B_119, A_120, A_120, E_121, k6_partfun1(A_120))=k5_relat_1(E_121, k6_partfun1(A_120)) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(resolution, [status(thm)], [c_28, c_302])).
% 2.60/1.36  tff(c_379, plain, (![A_120]: (k4_relset_1('#skF_1', '#skF_2', A_120, A_120, '#skF_3', k6_partfun1(A_120))=k5_relat_1('#skF_3', k6_partfun1(A_120)))), inference(resolution, [status(thm)], [c_34, c_373])).
% 2.60/1.36  tff(c_81, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.36  tff(c_89, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.60/1.36  tff(c_131, plain, (![A_58, B_59, D_60]: (r2_relset_1(A_58, B_59, D_60, D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.60/1.36  tff(c_137, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_131])).
% 2.60/1.36  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.36  tff(c_10, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.36  tff(c_105, plain, (![A_54, B_55]: (k5_relat_1(k6_partfun1(A_54), B_55)=B_55 | ~r1_tarski(k1_relat_1(B_55), A_54) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.60/1.36  tff(c_109, plain, (![A_1, B_2]: (k5_relat_1(k6_partfun1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_105])).
% 2.60/1.36  tff(c_160, plain, (![E_72, B_70, F_71, C_68, A_73, D_69]: (k4_relset_1(A_73, B_70, C_68, D_69, E_72, F_71)=k5_relat_1(E_72, F_71) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(C_68, D_69))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_70))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.36  tff(c_167, plain, (![A_74, B_75, E_76]: (k4_relset_1(A_74, B_75, '#skF_1', '#skF_2', E_76, '#skF_3')=k5_relat_1(E_76, '#skF_3') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(resolution, [status(thm)], [c_34, c_160])).
% 2.60/1.36  tff(c_174, plain, (![A_25]: (k4_relset_1(A_25, A_25, '#skF_1', '#skF_2', k6_partfun1(A_25), '#skF_3')=k5_relat_1(k6_partfun1(A_25), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_167])).
% 2.60/1.36  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.60/1.36  tff(c_60, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.60/1.36  tff(c_180, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_60])).
% 2.60/1.36  tff(c_192, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_180])).
% 2.60/1.36  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_89, c_137, c_192])).
% 2.60/1.36  tff(c_196, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.60/1.36  tff(c_380, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_196])).
% 2.60/1.36  tff(c_392, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_232, c_380])).
% 2.60/1.36  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_206, c_274, c_392])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 0
% 2.60/1.36  #Sup     : 72
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 2
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 2
% 2.60/1.36  #Demod        : 46
% 2.60/1.36  #Tautology    : 38
% 2.60/1.36  #SimpNegUnit  : 0
% 2.60/1.36  #BackRed      : 4
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.36  Timing (in seconds)
% 2.60/1.36  ----------------------
% 2.60/1.36  Preprocessing        : 0.33
% 2.60/1.36  Parsing              : 0.17
% 2.60/1.36  CNF conversion       : 0.02
% 2.60/1.36  Main loop            : 0.26
% 2.60/1.36  Inferencing          : 0.10
% 2.60/1.36  Reduction            : 0.08
% 2.60/1.36  Demodulation         : 0.06
% 2.60/1.36  BG Simplification    : 0.02
% 2.60/1.36  Subsumption          : 0.04
% 2.60/1.36  Abstraction          : 0.02
% 2.60/1.36  MUC search           : 0.00
% 2.60/1.36  Cooper               : 0.00
% 2.60/1.36  Total                : 0.62
% 2.60/1.36  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
