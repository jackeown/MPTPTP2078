%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:14 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 346 expanded)
%              Number of leaves         :   48 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          :  226 (1016 expanded)
%              Number of equality atoms :   60 ( 281 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_141,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_59,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_112,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_112])).

tff(c_130,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_121])).

tff(c_137,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_149,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_137])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_118,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_112])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_148,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_137])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_165,plain,(
    ! [A_74] :
      ( k4_relat_1(A_74) = k2_funct_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_171,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_177,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_76,c_171])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = B_20
      | ~ r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_178,plain,(
    ! [A_75,B_76] :
      ( k5_relat_1(k6_partfun1(A_75),B_76) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_182,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_24,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_80,plain,(
    ! [A_23] : v1_relat_1(k6_partfun1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24])).

tff(c_14,plain,(
    ! [A_18] : k4_relat_1(k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [A_18] : k4_relat_1(k6_partfun1(A_18)) = k6_partfun1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_14])).

tff(c_226,plain,(
    ! [B_87,A_88] :
      ( k5_relat_1(k4_relat_1(B_87),k4_relat_1(A_88)) = k4_relat_1(k5_relat_1(A_88,B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_235,plain,(
    ! [A_88] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_88)) = k4_relat_1(k5_relat_1(A_88,'#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_226])).

tff(c_268,plain,(
    ! [A_90] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_90)) = k4_relat_1(k5_relat_1(A_90,'#skF_3'))
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_235])).

tff(c_280,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_18)) = k4_relat_1(k5_relat_1(k6_partfun1(A_18),'#skF_3'))
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_268])).

tff(c_286,plain,(
    ! [A_18] : k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_18)) = k4_relat_1(k5_relat_1(k6_partfun1(A_18),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_280])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1410,plain,(
    ! [A_163,E_166,C_165,D_167,B_168,F_164] :
      ( m1_subset_1(k1_partfun1(A_163,B_168,C_165,D_167,E_166,F_164),k1_zfmisc_1(k2_zfmisc_1(A_163,D_167)))
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(C_165,D_167)))
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_163,B_168)))
      | ~ v1_funct_1(E_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_761,plain,(
    ! [D_116,C_117,A_118,B_119] :
      ( D_116 = C_117
      | ~ r2_relset_1(A_118,B_119,C_117,D_116)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_769,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_761])).

tff(c_784,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_769])).

tff(c_895,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_784])).

tff(c_1426,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1410,c_895])).

tff(c_1455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1426])).

tff(c_1456,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_784])).

tff(c_2649,plain,(
    ! [A_225,C_227,E_222,D_223,B_224,F_226] :
      ( k1_partfun1(A_225,B_224,C_227,D_223,E_222,F_226) = k5_relat_1(E_222,F_226)
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(C_227,D_223)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224)))
      | ~ v1_funct_1(E_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2655,plain,(
    ! [A_225,B_224,E_222] :
      ( k1_partfun1(A_225,B_224,'#skF_2','#skF_1',E_222,'#skF_4') = k5_relat_1(E_222,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224)))
      | ~ v1_funct_1(E_222) ) ),
    inference(resolution,[status(thm)],[c_66,c_2649])).

tff(c_2994,plain,(
    ! [A_241,B_242,E_243] :
      ( k1_partfun1(A_241,B_242,'#skF_2','#skF_1',E_243,'#skF_4') = k5_relat_1(E_243,'#skF_4')
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(E_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2655])).

tff(c_3003,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2994])).

tff(c_3011,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1456,c_3003])).

tff(c_22,plain,(
    ! [A_22] :
      ( v1_relat_1(k2_funct_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_238,plain,(
    ! [B_87] :
      ( k5_relat_1(k4_relat_1(B_87),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_226])).

tff(c_300,plain,(
    ! [B_92] :
      ( k5_relat_1(k4_relat_1(B_92),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_238])).

tff(c_312,plain,(
    ! [A_18] :
      ( k5_relat_1(k6_partfun1(A_18),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_18)))
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_300])).

tff(c_319,plain,(
    ! [A_93] : k5_relat_1(k6_partfun1(A_93),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_93))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_312])).

tff(c_332,plain,(
    ! [A_4] :
      ( k4_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_4))) = k2_funct_1('#skF_3')
      | ~ v4_relat_1(k2_funct_1('#skF_3'),A_4)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_319])).

tff(c_618,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_621,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_618])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_76,c_621])).

tff(c_627,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_208,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_214,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_208])).

tff(c_220,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_214])).

tff(c_28,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_relat_1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_partfun1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_529,plain,(
    ! [A_110,B_111,C_112] :
      ( k5_relat_1(k5_relat_1(A_110,B_111),C_112) = k5_relat_1(A_110,k5_relat_1(B_111,C_112))
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4169,plain,(
    ! [A_268,C_269] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_268)),C_269) = k5_relat_1(k2_funct_1(A_268),k5_relat_1(A_268,C_269))
      | ~ v1_relat_1(C_269)
      | ~ v1_relat_1(A_268)
      | ~ v1_relat_1(k2_funct_1(A_268))
      | ~ v2_funct_1(A_268)
      | ~ v1_funct_1(A_268)
      | ~ v1_relat_1(A_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_529])).

tff(c_4389,plain,(
    ! [C_269] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_269)) = k5_relat_1(k6_partfun1('#skF_2'),C_269)
      | ~ v1_relat_1(C_269)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_4169])).

tff(c_5449,plain,(
    ! [C_306] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_306)) = k5_relat_1(k6_partfun1('#skF_2'),C_306)
      | ~ v1_relat_1(C_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_76,c_60,c_627,c_127,c_4389])).

tff(c_5485,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3011,c_5449])).

tff(c_5505,plain,(
    k4_relat_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_286,c_5485])).

tff(c_5542,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k4_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_5505])).

tff(c_5550,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_148,c_177,c_5542])).

tff(c_5567,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5550,c_182])).

tff(c_5582,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_149,c_5567])).

tff(c_5584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:45:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.42/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.49  
% 7.42/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.49  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.42/2.49  
% 7.42/2.49  %Foreground sorts:
% 7.42/2.49  
% 7.42/2.49  
% 7.42/2.49  %Background operators:
% 7.42/2.49  
% 7.42/2.49  
% 7.42/2.49  %Foreground operators:
% 7.42/2.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.42/2.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.42/2.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.42/2.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.42/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.42/2.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.42/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.42/2.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.42/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.42/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.42/2.49  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.42/2.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.42/2.49  tff('#skF_2', type, '#skF_2': $i).
% 7.42/2.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.42/2.49  tff('#skF_3', type, '#skF_3': $i).
% 7.42/2.49  tff('#skF_1', type, '#skF_1': $i).
% 7.42/2.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.42/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.42/2.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.42/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.42/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.42/2.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.42/2.49  tff('#skF_4', type, '#skF_4': $i).
% 7.42/2.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.42/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.42/2.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.42/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.42/2.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.42/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.42/2.49  
% 7.50/2.51  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.50/2.51  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.50/2.51  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.50/2.51  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.50/2.51  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 7.50/2.51  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.50/2.51  tff(f_141, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.50/2.51  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 7.50/2.51  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.50/2.51  tff(f_59, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 7.50/2.51  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 7.50/2.51  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.50/2.51  tff(f_129, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.50/2.51  tff(f_113, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.50/2.51  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.50/2.51  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.50/2.51  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.50/2.51  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.50/2.51  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.50/2.51  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.50/2.51  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_112, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.50/2.51  tff(c_121, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_112])).
% 7.50/2.51  tff(c_130, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_121])).
% 7.50/2.51  tff(c_137, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.50/2.51  tff(c_149, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_137])).
% 7.50/2.51  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_118, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_112])).
% 7.50/2.51  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 7.50/2.51  tff(c_148, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_137])).
% 7.50/2.51  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_165, plain, (![A_74]: (k4_relat_1(A_74)=k2_funct_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.50/2.51  tff(c_171, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_165])).
% 7.50/2.51  tff(c_177, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_76, c_171])).
% 7.50/2.51  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.50/2.51  tff(c_52, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.50/2.51  tff(c_16, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=B_20 | ~r1_tarski(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.50/2.51  tff(c_178, plain, (![A_75, B_76]: (k5_relat_1(k6_partfun1(A_75), B_76)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_75) | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 7.50/2.51  tff(c_182, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_178])).
% 7.50/2.51  tff(c_24, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.50/2.51  tff(c_80, plain, (![A_23]: (v1_relat_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_24])).
% 7.50/2.51  tff(c_14, plain, (![A_18]: (k4_relat_1(k6_relat_1(A_18))=k6_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.50/2.51  tff(c_82, plain, (![A_18]: (k4_relat_1(k6_partfun1(A_18))=k6_partfun1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_14])).
% 7.50/2.51  tff(c_226, plain, (![B_87, A_88]: (k5_relat_1(k4_relat_1(B_87), k4_relat_1(A_88))=k4_relat_1(k5_relat_1(A_88, B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.50/2.51  tff(c_235, plain, (![A_88]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_88))=k4_relat_1(k5_relat_1(A_88, '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_177, c_226])).
% 7.50/2.51  tff(c_268, plain, (![A_90]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_90))=k4_relat_1(k5_relat_1(A_90, '#skF_3')) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_235])).
% 7.50/2.51  tff(c_280, plain, (![A_18]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_18))=k4_relat_1(k5_relat_1(k6_partfun1(A_18), '#skF_3')) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_268])).
% 7.50/2.51  tff(c_286, plain, (![A_18]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_18))=k4_relat_1(k5_relat_1(k6_partfun1(A_18), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_280])).
% 7.50/2.51  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_1410, plain, (![A_163, E_166, C_165, D_167, B_168, F_164]: (m1_subset_1(k1_partfun1(A_163, B_168, C_165, D_167, E_166, F_164), k1_zfmisc_1(k2_zfmisc_1(A_163, D_167))) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(C_165, D_167))) | ~v1_funct_1(F_164) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_163, B_168))) | ~v1_funct_1(E_166))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.50/2.51  tff(c_48, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.50/2.51  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_761, plain, (![D_116, C_117, A_118, B_119]: (D_116=C_117 | ~r2_relset_1(A_118, B_119, C_117, D_116) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.50/2.51  tff(c_769, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_761])).
% 7.50/2.51  tff(c_784, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_769])).
% 7.50/2.51  tff(c_895, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_784])).
% 7.50/2.51  tff(c_1426, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1410, c_895])).
% 7.50/2.51  tff(c_1455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1426])).
% 7.50/2.51  tff(c_1456, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_784])).
% 7.50/2.51  tff(c_2649, plain, (![A_225, C_227, E_222, D_223, B_224, F_226]: (k1_partfun1(A_225, B_224, C_227, D_223, E_222, F_226)=k5_relat_1(E_222, F_226) | ~m1_subset_1(F_226, k1_zfmisc_1(k2_zfmisc_1(C_227, D_223))) | ~v1_funct_1(F_226) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))) | ~v1_funct_1(E_222))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.50/2.51  tff(c_2655, plain, (![A_225, B_224, E_222]: (k1_partfun1(A_225, B_224, '#skF_2', '#skF_1', E_222, '#skF_4')=k5_relat_1(E_222, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))) | ~v1_funct_1(E_222))), inference(resolution, [status(thm)], [c_66, c_2649])).
% 7.50/2.51  tff(c_2994, plain, (![A_241, B_242, E_243]: (k1_partfun1(A_241, B_242, '#skF_2', '#skF_1', E_243, '#skF_4')=k5_relat_1(E_243, '#skF_4') | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~v1_funct_1(E_243))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2655])).
% 7.50/2.51  tff(c_3003, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2994])).
% 7.50/2.51  tff(c_3011, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1456, c_3003])).
% 7.50/2.51  tff(c_22, plain, (![A_22]: (v1_relat_1(k2_funct_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.50/2.51  tff(c_238, plain, (![B_87]: (k5_relat_1(k4_relat_1(B_87), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_226])).
% 7.50/2.51  tff(c_300, plain, (![B_92]: (k5_relat_1(k4_relat_1(B_92), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_92)) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_238])).
% 7.50/2.51  tff(c_312, plain, (![A_18]: (k5_relat_1(k6_partfun1(A_18), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_18))) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_300])).
% 7.50/2.51  tff(c_319, plain, (![A_93]: (k5_relat_1(k6_partfun1(A_93), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_93))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_312])).
% 7.50/2.51  tff(c_332, plain, (![A_4]: (k4_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_4)))=k2_funct_1('#skF_3') | ~v4_relat_1(k2_funct_1('#skF_3'), A_4) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_319])).
% 7.50/2.51  tff(c_618, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_332])).
% 7.50/2.51  tff(c_621, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_618])).
% 7.50/2.51  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_76, c_621])).
% 7.50/2.51  tff(c_627, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_332])).
% 7.50/2.51  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.50/2.51  tff(c_208, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.50/2.51  tff(c_214, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_208])).
% 7.50/2.51  tff(c_220, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_214])).
% 7.50/2.51  tff(c_28, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_relat_1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.50/2.51  tff(c_78, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_partfun1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 7.50/2.51  tff(c_529, plain, (![A_110, B_111, C_112]: (k5_relat_1(k5_relat_1(A_110, B_111), C_112)=k5_relat_1(A_110, k5_relat_1(B_111, C_112)) | ~v1_relat_1(C_112) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.50/2.51  tff(c_4169, plain, (![A_268, C_269]: (k5_relat_1(k6_partfun1(k2_relat_1(A_268)), C_269)=k5_relat_1(k2_funct_1(A_268), k5_relat_1(A_268, C_269)) | ~v1_relat_1(C_269) | ~v1_relat_1(A_268) | ~v1_relat_1(k2_funct_1(A_268)) | ~v2_funct_1(A_268) | ~v1_funct_1(A_268) | ~v1_relat_1(A_268))), inference(superposition, [status(thm), theory('equality')], [c_78, c_529])).
% 7.50/2.51  tff(c_4389, plain, (![C_269]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_269))=k5_relat_1(k6_partfun1('#skF_2'), C_269) | ~v1_relat_1(C_269) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_4169])).
% 7.50/2.51  tff(c_5449, plain, (![C_306]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_306))=k5_relat_1(k6_partfun1('#skF_2'), C_306) | ~v1_relat_1(C_306))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_76, c_60, c_627, c_127, c_4389])).
% 7.50/2.51  tff(c_5485, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3011, c_5449])).
% 7.50/2.51  tff(c_5505, plain, (k4_relat_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_286, c_5485])).
% 7.50/2.51  tff(c_5542, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k4_relat_1('#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_5505])).
% 7.50/2.51  tff(c_5550, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_148, c_177, c_5542])).
% 7.50/2.51  tff(c_5567, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5550, c_182])).
% 7.50/2.51  tff(c_5582, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_149, c_5567])).
% 7.50/2.51  tff(c_5584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5582])).
% 7.50/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/2.51  
% 7.50/2.51  Inference rules
% 7.50/2.51  ----------------------
% 7.50/2.51  #Ref     : 0
% 7.50/2.51  #Sup     : 1239
% 7.50/2.51  #Fact    : 0
% 7.50/2.51  #Define  : 0
% 7.50/2.51  #Split   : 4
% 7.50/2.51  #Chain   : 0
% 7.50/2.51  #Close   : 0
% 7.50/2.51  
% 7.50/2.51  Ordering : KBO
% 7.50/2.51  
% 7.50/2.51  Simplification rules
% 7.50/2.51  ----------------------
% 7.50/2.51  #Subsume      : 60
% 7.50/2.51  #Demod        : 1304
% 7.50/2.51  #Tautology    : 354
% 7.50/2.51  #SimpNegUnit  : 2
% 7.50/2.52  #BackRed      : 12
% 7.50/2.52  
% 7.50/2.52  #Partial instantiations: 0
% 7.50/2.52  #Strategies tried      : 1
% 7.50/2.52  
% 7.50/2.52  Timing (in seconds)
% 7.50/2.52  ----------------------
% 7.60/2.52  Preprocessing        : 0.35
% 7.60/2.52  Parsing              : 0.19
% 7.60/2.52  CNF conversion       : 0.02
% 7.60/2.52  Main loop            : 1.40
% 7.60/2.52  Inferencing          : 0.43
% 7.60/2.52  Reduction            : 0.58
% 7.60/2.52  Demodulation         : 0.45
% 7.60/2.52  BG Simplification    : 0.06
% 7.60/2.52  Subsumption          : 0.25
% 7.60/2.52  Abstraction          : 0.07
% 7.60/2.52  MUC search           : 0.00
% 7.60/2.52  Cooper               : 0.00
% 7.60/2.52  Total                : 1.80
% 7.60/2.52  Index Insertion      : 0.00
% 7.60/2.52  Index Deletion       : 0.00
% 7.60/2.52  Index Matching       : 0.00
% 7.60/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
