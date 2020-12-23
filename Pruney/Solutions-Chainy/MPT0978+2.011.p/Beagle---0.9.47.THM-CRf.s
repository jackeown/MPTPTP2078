%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 171 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 432 expanded)
%              Number of equality atoms :   38 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_119,negated_conjecture,(
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

tff(f_101,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_89,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

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

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_226,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_239,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_244,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_42])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_98,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_107,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_98])).

tff(c_116,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_107])).

tff(c_117,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_129,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_40,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_417,plain,(
    ! [A_110,D_108,B_109,C_112,E_113,F_111] :
      ( k4_relset_1(A_110,B_109,C_112,D_108,E_113,F_111) = k5_relat_1(E_113,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_112,D_108)))
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_448,plain,(
    ! [A_117,B_118,E_119] :
      ( k4_relset_1(A_117,B_118,'#skF_1','#skF_2',E_119,'#skF_3') = k5_relat_1(E_119,'#skF_3')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(resolution,[status(thm)],[c_52,c_417])).

tff(c_459,plain,(
    k4_relset_1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_448])).

tff(c_498,plain,(
    ! [B_126,F_127,E_129,A_125,D_128,C_124] :
      ( m1_subset_1(k4_relset_1(A_125,B_126,C_124,D_128,E_129,F_127),k1_zfmisc_1(k2_zfmisc_1(A_125,D_128)))
      | ~ m1_subset_1(F_127,k1_zfmisc_1(k2_zfmisc_1(C_124,D_128)))
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_532,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_498])).

tff(c_556,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52,c_532])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_634,plain,(
    ! [A_130,D_133,B_131,E_134,F_132,C_135] :
      ( k1_partfun1(A_130,B_131,C_135,D_133,E_134,F_132) = k5_relat_1(E_134,F_132)
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_135,D_133)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_646,plain,(
    ! [A_130,B_131,E_134] :
      ( k1_partfun1(A_130,B_131,'#skF_1','#skF_2',E_134,'#skF_3') = k5_relat_1(E_134,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(E_134) ) ),
    inference(resolution,[status(thm)],[c_52,c_634])).

tff(c_863,plain,(
    ! [A_147,B_148,E_149] :
      ( k1_partfun1(A_147,B_148,'#skF_1','#skF_2',E_149,'#skF_3') = k5_relat_1(E_149,'#skF_3')
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_funct_1(E_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_646])).

tff(c_890,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_863])).

tff(c_904,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_890])).

tff(c_36,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_303,plain,(
    ! [D_90,C_91,A_92,B_93] :
      ( D_90 = C_91
      | ~ r2_relset_1(A_92,B_93,C_91,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_311,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_303])).

tff(c_326,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_311])).

tff(c_340,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_926,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_340])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_926])).

tff(c_931,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_1222,plain,(
    ! [A_178,D_181,F_180,B_179,C_183,E_182] :
      ( k1_partfun1(A_178,B_179,C_183,D_181,E_182,F_180) = k5_relat_1(E_182,F_180)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_183,D_181)))
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(E_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1234,plain,(
    ! [A_178,B_179,E_182] :
      ( k1_partfun1(A_178,B_179,'#skF_1','#skF_2',E_182,'#skF_3') = k5_relat_1(E_182,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(E_182) ) ),
    inference(resolution,[status(thm)],[c_52,c_1222])).

tff(c_1422,plain,(
    ! [A_194,B_195,E_196] :
      ( k1_partfun1(A_194,B_195,'#skF_1','#skF_2',E_196,'#skF_3') = k5_relat_1(E_196,'#skF_3')
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_1(E_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1234])).

tff(c_1449,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1422])).

tff(c_1463,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_931,c_1449])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k2_relat_1(B_64),A_65)
      | ~ v5_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [B_86,A_87] :
      ( k2_relat_1(B_86) = A_87
      | ~ r1_tarski(A_87,k2_relat_1(B_86))
      | ~ v5_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_278,plain,(
    ! [A_10,B_12] :
      ( k2_relat_1(k5_relat_1(A_10,B_12)) = k2_relat_1(B_12)
      | ~ v5_relat_1(B_12,k2_relat_1(k5_relat_1(A_10,B_12)))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_258])).

tff(c_1482,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_278])).

tff(c_1495,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_116,c_129,c_58,c_58,c_1463,c_1482])).

tff(c_1497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_1495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:27:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.62  
% 3.76/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.76/1.63  
% 3.76/1.63  %Foreground sorts:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Background operators:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Foreground operators:
% 3.76/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.76/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.76/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.76/1.63  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.76/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.76/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.76/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.76/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.76/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.76/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.76/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.76/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.63  
% 3.76/1.64  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.76/1.64  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.76/1.64  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.76/1.64  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.76/1.64  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.76/1.64  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.76/1.64  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.76/1.64  tff(f_79, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.76/1.64  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.76/1.64  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.76/1.64  tff(f_89, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.76/1.64  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.76/1.64  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.76/1.64  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.76/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.76/1.64  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.76/1.64  tff(c_226, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.76/1.64  tff(c_239, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_226])).
% 3.76/1.64  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.76/1.64  tff(c_244, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_42])).
% 3.76/1.64  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.76/1.64  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.76/1.64  tff(c_98, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.76/1.64  tff(c_104, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_98])).
% 3.76/1.64  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_104])).
% 3.76/1.64  tff(c_107, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_98])).
% 3.76/1.64  tff(c_116, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_107])).
% 3.76/1.64  tff(c_117, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.76/1.64  tff(c_129, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_117])).
% 3.76/1.64  tff(c_40, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.76/1.64  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.76/1.64  tff(c_58, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 3.76/1.64  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.76/1.64  tff(c_417, plain, (![A_110, D_108, B_109, C_112, E_113, F_111]: (k4_relset_1(A_110, B_109, C_112, D_108, E_113, F_111)=k5_relat_1(E_113, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_112, D_108))) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.64  tff(c_448, plain, (![A_117, B_118, E_119]: (k4_relset_1(A_117, B_118, '#skF_1', '#skF_2', E_119, '#skF_3')=k5_relat_1(E_119, '#skF_3') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(resolution, [status(thm)], [c_52, c_417])).
% 3.76/1.64  tff(c_459, plain, (k4_relset_1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_448])).
% 3.76/1.64  tff(c_498, plain, (![B_126, F_127, E_129, A_125, D_128, C_124]: (m1_subset_1(k4_relset_1(A_125, B_126, C_124, D_128, E_129, F_127), k1_zfmisc_1(k2_zfmisc_1(A_125, D_128))) | ~m1_subset_1(F_127, k1_zfmisc_1(k2_zfmisc_1(C_124, D_128))) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.76/1.64  tff(c_532, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_459, c_498])).
% 3.76/1.64  tff(c_556, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52, c_532])).
% 3.76/1.64  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.76/1.64  tff(c_634, plain, (![A_130, D_133, B_131, E_134, F_132, C_135]: (k1_partfun1(A_130, B_131, C_135, D_133, E_134, F_132)=k5_relat_1(E_134, F_132) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_135, D_133))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.76/1.64  tff(c_646, plain, (![A_130, B_131, E_134]: (k1_partfun1(A_130, B_131, '#skF_1', '#skF_2', E_134, '#skF_3')=k5_relat_1(E_134, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(E_134))), inference(resolution, [status(thm)], [c_52, c_634])).
% 3.76/1.64  tff(c_863, plain, (![A_147, B_148, E_149]: (k1_partfun1(A_147, B_148, '#skF_1', '#skF_2', E_149, '#skF_3')=k5_relat_1(E_149, '#skF_3') | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_funct_1(E_149))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_646])).
% 3.76/1.64  tff(c_890, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_863])).
% 3.76/1.64  tff(c_904, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_890])).
% 3.76/1.64  tff(c_36, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.76/1.64  tff(c_57, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.76/1.64  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.76/1.64  tff(c_303, plain, (![D_90, C_91, A_92, B_93]: (D_90=C_91 | ~r2_relset_1(A_92, B_93, C_91, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.76/1.64  tff(c_311, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_303])).
% 3.76/1.64  tff(c_326, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_311])).
% 3.76/1.64  tff(c_340, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_326])).
% 3.76/1.64  tff(c_926, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_904, c_340])).
% 3.76/1.64  tff(c_930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_926])).
% 3.76/1.64  tff(c_931, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_326])).
% 3.76/1.64  tff(c_1222, plain, (![A_178, D_181, F_180, B_179, C_183, E_182]: (k1_partfun1(A_178, B_179, C_183, D_181, E_182, F_180)=k5_relat_1(E_182, F_180) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(C_183, D_181))) | ~v1_funct_1(F_180) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(E_182))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.76/1.64  tff(c_1234, plain, (![A_178, B_179, E_182]: (k1_partfun1(A_178, B_179, '#skF_1', '#skF_2', E_182, '#skF_3')=k5_relat_1(E_182, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(E_182))), inference(resolution, [status(thm)], [c_52, c_1222])).
% 3.76/1.64  tff(c_1422, plain, (![A_194, B_195, E_196]: (k1_partfun1(A_194, B_195, '#skF_1', '#skF_2', E_196, '#skF_3')=k5_relat_1(E_196, '#skF_3') | ~m1_subset_1(E_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_1(E_196))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1234])).
% 3.76/1.64  tff(c_1449, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1422])).
% 3.76/1.64  tff(c_1463, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_931, c_1449])).
% 3.76/1.64  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.76/1.64  tff(c_149, plain, (![B_64, A_65]: (r1_tarski(k2_relat_1(B_64), A_65) | ~v5_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.76/1.64  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.64  tff(c_258, plain, (![B_86, A_87]: (k2_relat_1(B_86)=A_87 | ~r1_tarski(A_87, k2_relat_1(B_86)) | ~v5_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_149, c_2])).
% 3.76/1.64  tff(c_278, plain, (![A_10, B_12]: (k2_relat_1(k5_relat_1(A_10, B_12))=k2_relat_1(B_12) | ~v5_relat_1(B_12, k2_relat_1(k5_relat_1(A_10, B_12))) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_16, c_258])).
% 3.76/1.64  tff(c_1482, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1463, c_278])).
% 3.76/1.64  tff(c_1495, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_116, c_129, c_58, c_58, c_1463, c_1482])).
% 3.76/1.64  tff(c_1497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_1495])).
% 3.76/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.64  
% 3.76/1.64  Inference rules
% 3.76/1.64  ----------------------
% 3.76/1.64  #Ref     : 0
% 3.76/1.64  #Sup     : 332
% 3.76/1.64  #Fact    : 0
% 3.76/1.64  #Define  : 0
% 3.76/1.64  #Split   : 1
% 3.76/1.64  #Chain   : 0
% 3.76/1.64  #Close   : 0
% 3.76/1.64  
% 3.76/1.64  Ordering : KBO
% 3.76/1.64  
% 3.76/1.64  Simplification rules
% 3.76/1.64  ----------------------
% 3.76/1.64  #Subsume      : 15
% 3.76/1.64  #Demod        : 164
% 3.76/1.64  #Tautology    : 85
% 3.76/1.64  #SimpNegUnit  : 2
% 3.76/1.64  #BackRed      : 9
% 3.76/1.64  
% 3.76/1.64  #Partial instantiations: 0
% 3.76/1.64  #Strategies tried      : 1
% 3.76/1.64  
% 3.76/1.64  Timing (in seconds)
% 3.76/1.64  ----------------------
% 3.76/1.65  Preprocessing        : 0.33
% 3.76/1.65  Parsing              : 0.17
% 3.76/1.65  CNF conversion       : 0.02
% 3.76/1.65  Main loop            : 0.55
% 3.76/1.65  Inferencing          : 0.20
% 3.76/1.65  Reduction            : 0.18
% 3.76/1.65  Demodulation         : 0.13
% 3.76/1.65  BG Simplification    : 0.03
% 3.76/1.65  Subsumption          : 0.10
% 3.76/1.65  Abstraction          : 0.03
% 3.76/1.65  MUC search           : 0.00
% 3.76/1.65  Cooper               : 0.00
% 3.76/1.65  Total                : 0.91
% 3.76/1.65  Index Insertion      : 0.00
% 3.76/1.65  Index Deletion       : 0.00
% 3.76/1.65  Index Matching       : 0.00
% 3.76/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
