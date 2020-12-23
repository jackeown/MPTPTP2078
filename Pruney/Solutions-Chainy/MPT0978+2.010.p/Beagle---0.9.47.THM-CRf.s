%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 163 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 426 expanded)
%              Number of equality atoms :   38 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_228,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_240,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_228])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_251,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_44])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_93,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_130,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_141,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_130])).

tff(c_42,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_411,plain,(
    ! [A_109,B_108,C_111,D_107,F_110,E_112] :
      ( k4_relset_1(A_109,B_108,C_111,D_107,E_112,F_110) = k5_relat_1(E_112,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_111,D_107)))
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_421,plain,(
    ! [A_113,B_114,E_115] :
      ( k4_relset_1(A_113,B_114,'#skF_1','#skF_2',E_115,'#skF_3') = k5_relat_1(E_115,'#skF_3')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(resolution,[status(thm)],[c_54,c_411])).

tff(c_433,plain,(
    k4_relset_1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_421])).

tff(c_489,plain,(
    ! [A_124,D_127,B_125,C_123,F_126,E_128] :
      ( m1_subset_1(k4_relset_1(A_124,B_125,C_123,D_127,E_128,F_126),k1_zfmisc_1(k2_zfmisc_1(A_124,D_127)))
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_123,D_127)))
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_526,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_489])).

tff(c_549,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54,c_526])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_625,plain,(
    ! [E_133,F_131,D_132,C_134,B_130,A_129] :
      ( k1_partfun1(A_129,B_130,C_134,D_132,E_133,F_131) = k5_relat_1(E_133,F_131)
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_134,D_132)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_635,plain,(
    ! [A_129,B_130,E_133] :
      ( k1_partfun1(A_129,B_130,'#skF_1','#skF_2',E_133,'#skF_3') = k5_relat_1(E_133,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_133) ) ),
    inference(resolution,[status(thm)],[c_54,c_625])).

tff(c_914,plain,(
    ! [A_148,B_149,E_150] :
      ( k1_partfun1(A_148,B_149,'#skF_1','#skF_2',E_150,'#skF_3') = k5_relat_1(E_150,'#skF_3')
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_1(E_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_635])).

tff(c_944,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_914])).

tff(c_958,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_944])).

tff(c_38,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_286,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_294,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_46,c_286])).

tff(c_309,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_294])).

tff(c_336,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_963,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_336])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_963])).

tff(c_968,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_1276,plain,(
    ! [F_185,C_188,D_186,A_183,B_184,E_187] :
      ( k1_partfun1(A_183,B_184,C_188,D_186,E_187,F_185) = k5_relat_1(E_187,F_185)
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1(C_188,D_186)))
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1286,plain,(
    ! [A_183,B_184,E_187] :
      ( k1_partfun1(A_183,B_184,'#skF_1','#skF_2',E_187,'#skF_3') = k5_relat_1(E_187,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_187) ) ),
    inference(resolution,[status(thm)],[c_54,c_1276])).

tff(c_1378,plain,(
    ! [A_189,B_190,E_191] :
      ( k1_partfun1(A_189,B_190,'#skF_1','#skF_2',E_191,'#skF_3') = k5_relat_1(E_191,'#skF_3')
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_1(E_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1286])).

tff(c_1402,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1378])).

tff(c_1414,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_968,c_1402])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_260,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(B_87) = A_88
      | ~ r1_tarski(A_88,k2_relat_1(B_87))
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_280,plain,(
    ! [A_10,B_12] :
      ( k2_relat_1(k5_relat_1(A_10,B_12)) = k2_relat_1(B_12)
      | ~ v5_relat_1(B_12,k2_relat_1(k5_relat_1(A_10,B_12)))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_1430,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1414,c_280])).

tff(c_1443,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_108,c_141,c_59,c_59,c_1414,c_1430])).

tff(c_1445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_1443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.63  
% 3.77/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.77/1.63  
% 3.77/1.63  %Foreground sorts:
% 3.77/1.63  
% 3.77/1.63  
% 3.77/1.63  %Background operators:
% 3.77/1.63  
% 3.77/1.63  
% 3.77/1.63  %Foreground operators:
% 3.77/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.77/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.77/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.77/1.63  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.77/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.77/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.77/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.77/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.63  
% 3.77/1.65  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.77/1.65  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.77/1.65  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.77/1.65  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.77/1.65  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.77/1.65  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.77/1.65  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.77/1.65  tff(f_79, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.77/1.65  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.77/1.65  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.77/1.65  tff(f_91, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.77/1.65  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.77/1.65  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.77/1.65  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.77/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.77/1.65  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.65  tff(c_228, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.77/1.65  tff(c_240, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_228])).
% 3.77/1.65  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.65  tff(c_251, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_44])).
% 3.77/1.65  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.65  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.65  tff(c_93, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.77/1.65  tff(c_102, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_93])).
% 3.77/1.65  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 3.77/1.65  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_93])).
% 3.77/1.65  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_99])).
% 3.77/1.65  tff(c_130, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.77/1.65  tff(c_141, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_130])).
% 3.77/1.65  tff(c_42, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.77/1.65  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.77/1.65  tff(c_59, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20])).
% 3.77/1.65  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.65  tff(c_411, plain, (![A_109, B_108, C_111, D_107, F_110, E_112]: (k4_relset_1(A_109, B_108, C_111, D_107, E_112, F_110)=k5_relat_1(E_112, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_111, D_107))) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.77/1.65  tff(c_421, plain, (![A_113, B_114, E_115]: (k4_relset_1(A_113, B_114, '#skF_1', '#skF_2', E_115, '#skF_3')=k5_relat_1(E_115, '#skF_3') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(resolution, [status(thm)], [c_54, c_411])).
% 3.77/1.65  tff(c_433, plain, (k4_relset_1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_421])).
% 3.77/1.65  tff(c_489, plain, (![A_124, D_127, B_125, C_123, F_126, E_128]: (m1_subset_1(k4_relset_1(A_124, B_125, C_123, D_127, E_128, F_126), k1_zfmisc_1(k2_zfmisc_1(A_124, D_127))) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_123, D_127))) | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.77/1.65  tff(c_526, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_433, c_489])).
% 3.77/1.65  tff(c_549, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_54, c_526])).
% 3.77/1.65  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.65  tff(c_625, plain, (![E_133, F_131, D_132, C_134, B_130, A_129]: (k1_partfun1(A_129, B_130, C_134, D_132, E_133, F_131)=k5_relat_1(E_133, F_131) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_134, D_132))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.77/1.65  tff(c_635, plain, (![A_129, B_130, E_133]: (k1_partfun1(A_129, B_130, '#skF_1', '#skF_2', E_133, '#skF_3')=k5_relat_1(E_133, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_133))), inference(resolution, [status(thm)], [c_54, c_625])).
% 3.77/1.65  tff(c_914, plain, (![A_148, B_149, E_150]: (k1_partfun1(A_148, B_149, '#skF_1', '#skF_2', E_150, '#skF_3')=k5_relat_1(E_150, '#skF_3') | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_1(E_150))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_635])).
% 3.77/1.65  tff(c_944, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_914])).
% 3.77/1.65  tff(c_958, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_944])).
% 3.77/1.65  tff(c_38, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/1.65  tff(c_46, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.65  tff(c_286, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.77/1.65  tff(c_294, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_286])).
% 3.77/1.65  tff(c_309, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_294])).
% 3.77/1.65  tff(c_336, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_309])).
% 3.77/1.65  tff(c_963, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_336])).
% 3.77/1.65  tff(c_967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_549, c_963])).
% 3.77/1.65  tff(c_968, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_309])).
% 3.77/1.65  tff(c_1276, plain, (![F_185, C_188, D_186, A_183, B_184, E_187]: (k1_partfun1(A_183, B_184, C_188, D_186, E_187, F_185)=k5_relat_1(E_187, F_185) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1(C_188, D_186))) | ~v1_funct_1(F_185) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(E_187))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.77/1.65  tff(c_1286, plain, (![A_183, B_184, E_187]: (k1_partfun1(A_183, B_184, '#skF_1', '#skF_2', E_187, '#skF_3')=k5_relat_1(E_187, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(E_187))), inference(resolution, [status(thm)], [c_54, c_1276])).
% 3.77/1.65  tff(c_1378, plain, (![A_189, B_190, E_191]: (k1_partfun1(A_189, B_190, '#skF_1', '#skF_2', E_191, '#skF_3')=k5_relat_1(E_191, '#skF_3') | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_1(E_191))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1286])).
% 3.77/1.65  tff(c_1402, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1378])).
% 3.77/1.65  tff(c_1414, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_968, c_1402])).
% 3.77/1.65  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.77/1.65  tff(c_120, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.77/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.65  tff(c_260, plain, (![B_87, A_88]: (k2_relat_1(B_87)=A_88 | ~r1_tarski(A_88, k2_relat_1(B_87)) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_120, c_2])).
% 3.77/1.65  tff(c_280, plain, (![A_10, B_12]: (k2_relat_1(k5_relat_1(A_10, B_12))=k2_relat_1(B_12) | ~v5_relat_1(B_12, k2_relat_1(k5_relat_1(A_10, B_12))) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_16, c_260])).
% 3.77/1.65  tff(c_1430, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1414, c_280])).
% 3.77/1.65  tff(c_1443, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_108, c_141, c_59, c_59, c_1414, c_1430])).
% 3.77/1.65  tff(c_1445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_1443])).
% 3.77/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.65  
% 3.77/1.65  Inference rules
% 3.77/1.65  ----------------------
% 3.77/1.65  #Ref     : 0
% 3.77/1.65  #Sup     : 324
% 3.77/1.65  #Fact    : 0
% 3.77/1.65  #Define  : 0
% 3.77/1.65  #Split   : 1
% 3.77/1.65  #Chain   : 0
% 3.77/1.65  #Close   : 0
% 3.77/1.65  
% 3.77/1.65  Ordering : KBO
% 3.77/1.65  
% 3.77/1.65  Simplification rules
% 3.77/1.65  ----------------------
% 3.77/1.65  #Subsume      : 15
% 3.77/1.65  #Demod        : 162
% 3.77/1.65  #Tautology    : 96
% 3.77/1.65  #SimpNegUnit  : 2
% 3.77/1.65  #BackRed      : 9
% 3.77/1.65  
% 3.77/1.65  #Partial instantiations: 0
% 3.77/1.65  #Strategies tried      : 1
% 3.77/1.65  
% 3.77/1.65  Timing (in seconds)
% 3.77/1.65  ----------------------
% 3.77/1.65  Preprocessing        : 0.33
% 3.77/1.65  Parsing              : 0.18
% 3.77/1.65  CNF conversion       : 0.02
% 3.77/1.65  Main loop            : 0.54
% 3.77/1.65  Inferencing          : 0.20
% 3.77/1.65  Reduction            : 0.17
% 3.77/1.65  Demodulation         : 0.13
% 3.77/1.65  BG Simplification    : 0.03
% 3.77/1.65  Subsumption          : 0.09
% 3.77/1.65  Abstraction          : 0.03
% 3.77/1.65  MUC search           : 0.00
% 3.77/1.65  Cooper               : 0.00
% 3.77/1.65  Total                : 0.91
% 3.77/1.65  Index Insertion      : 0.00
% 3.77/1.65  Index Deletion       : 0.00
% 3.77/1.65  Index Matching       : 0.00
% 3.77/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
