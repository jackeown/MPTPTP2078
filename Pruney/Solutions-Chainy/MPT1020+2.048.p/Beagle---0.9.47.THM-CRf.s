%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:57 EST 2020

% Result     : Theorem 9.48s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :  310 (7616 expanded)
%              Number of leaves         :   44 (2393 expanded)
%              Depth                    :   21
%              Number of atoms          :  636 (22078 expanded)
%              Number of equality atoms :  167 (4423 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_176,axiom,(
    ! [A,B,C] :
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1064,plain,(
    ! [A_162,B_163,D_164] :
      ( r2_relset_1(A_162,B_163,D_164,D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1080,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1064])).

tff(c_86,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_84,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_80,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_234,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_249,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_234])).

tff(c_262,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_249])).

tff(c_263,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_286,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_263])).

tff(c_442,plain,(
    ! [B_99,A_100] :
      ( k2_relat_1(B_99) = A_100
      | ~ v2_funct_2(B_99,A_100)
      | ~ v5_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_457,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_442])).

tff(c_473,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_457])).

tff(c_477,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_82,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_835,plain,(
    ! [C_140,B_141,A_142] :
      ( v2_funct_2(C_140,B_141)
      | ~ v3_funct_2(C_140,A_142,B_141)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_848,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_835])).

tff(c_862,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_848])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_862])).

tff(c_865,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_1091,plain,(
    ! [A_167,B_168,C_169] :
      ( k2_relset_1(A_167,B_168,C_169) = k2_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1104,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1091])).

tff(c_1116,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_1104])).

tff(c_58,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1078,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_58,c_1064])).

tff(c_1135,plain,(
    ! [C_171,A_172,B_173] :
      ( v2_funct_1(C_171)
      | ~ v3_funct_2(C_171,A_172,B_173)
      | ~ v1_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1148,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1135])).

tff(c_1162,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1148])).

tff(c_1918,plain,(
    ! [D_264,A_261,E_260,F_259,B_263,C_262] :
      ( m1_subset_1(k1_partfun1(A_261,B_263,C_262,D_264,E_260,F_259),k1_zfmisc_1(k2_zfmisc_1(A_261,D_264)))
      | ~ m1_subset_1(F_259,k1_zfmisc_1(k2_zfmisc_1(C_262,D_264)))
      | ~ v1_funct_1(F_259)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_263)))
      | ~ v1_funct_1(E_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1224,plain,(
    ! [D_184,C_185,A_186,B_187] :
      ( D_184 = C_185
      | ~ r2_relset_1(A_186,B_187,C_185,D_184)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1236,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_1224])).

tff(c_1258,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1236])).

tff(c_1280,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1258])).

tff(c_1936,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1918,c_1280])).

tff(c_1978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_78,c_72,c_1936])).

tff(c_1979,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1258])).

tff(c_3501,plain,(
    ! [C_361,D_362,B_363,A_364] :
      ( k2_funct_1(C_361) = D_362
      | k1_xboole_0 = B_363
      | k1_xboole_0 = A_364
      | ~ v2_funct_1(C_361)
      | ~ r2_relset_1(A_364,A_364,k1_partfun1(A_364,B_363,B_363,A_364,C_361,D_362),k6_partfun1(A_364))
      | k2_relset_1(A_364,B_363,C_361) != B_363
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(B_363,A_364)))
      | ~ v1_funct_2(D_362,B_363,A_364)
      | ~ v1_funct_1(D_362)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_364,B_363)))
      | ~ v1_funct_2(C_361,A_364,B_363)
      | ~ v1_funct_1(C_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3504,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1979,c_3501])).

tff(c_3509,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1116,c_1078,c_1162,c_3504])).

tff(c_3512,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3509])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3544,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3543,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3512,c_14])).

tff(c_130,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_130])).

tff(c_173,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_173])).

tff(c_370,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_3691,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3543,c_370])).

tff(c_3699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3544,c_3691])).

tff(c_3700,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3509])).

tff(c_2125,plain,(
    ! [A_282,B_283] :
      ( k2_funct_2(A_282,B_283) = k2_funct_1(B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(k2_zfmisc_1(A_282,A_282)))
      | ~ v3_funct_2(B_283,A_282,A_282)
      | ~ v1_funct_2(B_283,A_282,A_282)
      | ~ v1_funct_1(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2138,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_2125])).

tff(c_2154,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_2138])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_2161,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_68])).

tff(c_3758,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3700,c_2161])).

tff(c_3777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_3758])).

tff(c_3778,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_3783,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3778,c_72])).

tff(c_3848,plain,(
    ! [A_375,B_376,D_377] :
      ( r2_relset_1(A_375,B_376,D_377,D_377)
      | ~ m1_subset_1(D_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5189,plain,(
    ! [D_530] :
      ( r2_relset_1('#skF_1','#skF_1',D_530,D_530)
      | ~ m1_subset_1(D_530,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_3848])).

tff(c_5202,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3783,c_5189])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3784,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3778,c_80])).

tff(c_3896,plain,(
    ! [B_383,A_384] :
      ( k2_relat_1(B_383) = A_384
      | ~ v2_funct_2(B_383,A_384)
      | ~ v5_relat_1(B_383,A_384)
      | ~ v1_relat_1(B_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3911,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_3896])).

tff(c_3925,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_3911])).

tff(c_3929,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3925])).

tff(c_4186,plain,(
    ! [C_416,B_417,A_418] :
      ( v2_funct_2(C_416,B_417)
      | ~ v3_funct_2(C_416,A_418,B_417)
      | ~ v1_funct_1(C_416)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_418,B_417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4465,plain,(
    ! [C_450] :
      ( v2_funct_2(C_450,'#skF_1')
      | ~ v3_funct_2(C_450,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_450)
      | ~ m1_subset_1(C_450,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_4186])).

tff(c_4471,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3784,c_4465])).

tff(c_4482,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_4471])).

tff(c_4484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3929,c_4482])).

tff(c_4485,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3925])).

tff(c_5147,plain,(
    ! [A_525,B_526,C_527] :
      ( k2_relset_1(A_525,B_526,C_527) = k2_relat_1(C_527)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5320,plain,(
    ! [C_545] :
      ( k2_relset_1('#skF_1','#skF_1',C_545) = k2_relat_1(C_545)
      | ~ m1_subset_1(C_545,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_5147])).

tff(c_5326,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3784,c_5320])).

tff(c_5337,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4485,c_5326])).

tff(c_5243,plain,(
    ! [C_536,A_537,B_538] :
      ( v2_funct_1(C_536)
      | ~ v3_funct_2(C_536,A_537,B_538)
      | ~ v1_funct_1(C_536)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5389,plain,(
    ! [C_556] :
      ( v2_funct_1(C_556)
      | ~ v3_funct_2(C_556,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_556)
      | ~ m1_subset_1(C_556,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_5243])).

tff(c_5395,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3784,c_5389])).

tff(c_5406,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_5395])).

tff(c_6561,plain,(
    ! [C_671,D_672,B_673,A_674] :
      ( k2_funct_1(C_671) = D_672
      | k1_xboole_0 = B_673
      | k1_xboole_0 = A_674
      | ~ v2_funct_1(C_671)
      | ~ r2_relset_1(A_674,A_674,k1_partfun1(A_674,B_673,B_673,A_674,C_671,D_672),k6_partfun1(A_674))
      | k2_relset_1(A_674,B_673,C_671) != B_673
      | ~ m1_subset_1(D_672,k1_zfmisc_1(k2_zfmisc_1(B_673,A_674)))
      | ~ v1_funct_2(D_672,B_673,A_674)
      | ~ v1_funct_1(D_672)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(A_674,B_673)))
      | ~ v1_funct_2(C_671,A_674,B_673)
      | ~ v1_funct_1(C_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_6564,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6561])).

tff(c_6570,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_3784,c_3778,c_78,c_76,c_3783,c_3778,c_5337,c_5406,c_6564])).

tff(c_6573,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6570])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3795,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_10])).

tff(c_3863,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3795])).

tff(c_6597,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6573,c_3863])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6610,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6573,c_6573,c_12])).

tff(c_6780,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6610,c_3778])).

tff(c_6782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6597,c_6780])).

tff(c_6783,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6570])).

tff(c_5679,plain,(
    ! [A_590,B_591] :
      ( k2_funct_2(A_590,B_591) = k2_funct_1(B_591)
      | ~ m1_subset_1(B_591,k1_zfmisc_1(k2_zfmisc_1(A_590,A_590)))
      | ~ v3_funct_2(B_591,A_590,A_590)
      | ~ v1_funct_2(B_591,A_590,A_590)
      | ~ v1_funct_1(B_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5951,plain,(
    ! [B_623] :
      ( k2_funct_2('#skF_1',B_623) = k2_funct_1(B_623)
      | ~ m1_subset_1(B_623,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_623,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_623,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_623) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_5679])).

tff(c_5957,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3784,c_5951])).

tff(c_5968,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_5957])).

tff(c_6051,plain,(
    ! [A_644,B_645] :
      ( m1_subset_1(k2_funct_2(A_644,B_645),k1_zfmisc_1(k2_zfmisc_1(A_644,A_644)))
      | ~ m1_subset_1(B_645,k1_zfmisc_1(k2_zfmisc_1(A_644,A_644)))
      | ~ v3_funct_2(B_645,A_644,A_644)
      | ~ v1_funct_2(B_645,A_644,A_644)
      | ~ v1_funct_1(B_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6092,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5968,c_6051])).

tff(c_6122,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_3784,c_3778,c_3778,c_6092])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6261,plain,(
    r1_tarski(k2_funct_1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6122,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6346,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6261,c_2])).

tff(c_6502,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6346])).

tff(c_6786,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6783,c_6502])).

tff(c_6804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6786])).

tff(c_6805,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6346])).

tff(c_5974,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_68])).

tff(c_6845,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6805,c_5974])).

tff(c_6861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5202,c_6845])).

tff(c_6863,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3795])).

tff(c_6879,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6863,c_8])).

tff(c_150,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_130])).

tff(c_187,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_173])).

tff(c_334,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_3780,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3778,c_334])).

tff(c_6910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_3780])).

tff(c_6911,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_6928,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6911,c_72])).

tff(c_8615,plain,(
    ! [A_881,B_882,D_883] :
      ( r2_relset_1(A_881,B_882,D_883,D_883)
      | ~ m1_subset_1(D_883,k1_zfmisc_1(k2_zfmisc_1(A_881,B_882))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8827,plain,(
    ! [D_909] :
      ( r2_relset_1('#skF_1','#skF_1',D_909,D_909)
      | ~ m1_subset_1(D_909,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_8615])).

tff(c_8840,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6928,c_8827])).

tff(c_6929,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6911,c_80])).

tff(c_6983,plain,(
    ! [B_685,A_686] :
      ( k2_relat_1(B_685) = A_686
      | ~ v2_funct_2(B_685,A_686)
      | ~ v5_relat_1(B_685,A_686)
      | ~ v1_relat_1(B_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6995,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_6983])).

tff(c_7008,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_6995])).

tff(c_7023,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7008])).

tff(c_7317,plain,(
    ! [C_725,B_726,A_727] :
      ( v2_funct_2(C_725,B_726)
      | ~ v3_funct_2(C_725,A_727,B_726)
      | ~ v1_funct_1(C_725)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_727,B_726))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7796,plain,(
    ! [C_786] :
      ( v2_funct_2(C_786,'#skF_1')
      | ~ v3_funct_2(C_786,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_786)
      | ~ m1_subset_1(C_786,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_7317])).

tff(c_7802,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6929,c_7796])).

tff(c_7813,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7802])).

tff(c_7815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7023,c_7813])).

tff(c_7816,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7008])).

tff(c_8668,plain,(
    ! [A_893,B_894,C_895] :
      ( k2_relset_1(A_893,B_894,C_895) = k2_relat_1(C_895)
      | ~ m1_subset_1(C_895,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8933,plain,(
    ! [C_924] :
      ( k2_relset_1('#skF_1','#skF_1',C_924) = k2_relat_1(C_924)
      | ~ m1_subset_1(C_924,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_8668])).

tff(c_8939,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6929,c_8933])).

tff(c_8950,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7816,c_8939])).

tff(c_8765,plain,(
    ! [C_902,A_903,B_904] :
      ( v2_funct_1(C_902)
      | ~ v3_funct_2(C_902,A_903,B_904)
      | ~ v1_funct_1(C_902)
      | ~ m1_subset_1(C_902,k1_zfmisc_1(k2_zfmisc_1(A_903,B_904))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9254,plain,(
    ! [C_963] :
      ( v2_funct_1(C_963)
      | ~ v3_funct_2(C_963,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_963)
      | ~ m1_subset_1(C_963,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_8765])).

tff(c_9260,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6929,c_9254])).

tff(c_9271,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_9260])).

tff(c_10094,plain,(
    ! [C_1038,D_1039,B_1040,A_1041] :
      ( k2_funct_1(C_1038) = D_1039
      | k1_xboole_0 = B_1040
      | k1_xboole_0 = A_1041
      | ~ v2_funct_1(C_1038)
      | ~ r2_relset_1(A_1041,A_1041,k1_partfun1(A_1041,B_1040,B_1040,A_1041,C_1038,D_1039),k6_partfun1(A_1041))
      | k2_relset_1(A_1041,B_1040,C_1038) != B_1040
      | ~ m1_subset_1(D_1039,k1_zfmisc_1(k2_zfmisc_1(B_1040,A_1041)))
      | ~ v1_funct_2(D_1039,B_1040,A_1041)
      | ~ v1_funct_1(D_1039)
      | ~ m1_subset_1(C_1038,k1_zfmisc_1(k2_zfmisc_1(A_1041,B_1040)))
      | ~ v1_funct_2(C_1038,A_1041,B_1040)
      | ~ v1_funct_1(C_1038) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_10097,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_10094])).

tff(c_10103,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_6929,c_6911,c_78,c_76,c_6928,c_6911,c_8950,c_9271,c_10097])).

tff(c_10106,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10103])).

tff(c_6940,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_10])).

tff(c_8614,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6940])).

tff(c_10133,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10106,c_8614])).

tff(c_10143,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10106,c_10106,c_12])).

tff(c_10381,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10143,c_6911])).

tff(c_10383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10133,c_10381])).

tff(c_10384,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10103])).

tff(c_9227,plain,(
    ! [A_960,B_961] :
      ( k2_funct_2(A_960,B_961) = k2_funct_1(B_961)
      | ~ m1_subset_1(B_961,k1_zfmisc_1(k2_zfmisc_1(A_960,A_960)))
      | ~ v3_funct_2(B_961,A_960,A_960)
      | ~ v1_funct_2(B_961,A_960,A_960)
      | ~ v1_funct_1(B_961) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_9569,plain,(
    ! [B_1012] :
      ( k2_funct_2('#skF_1',B_1012) = k2_funct_1(B_1012)
      | ~ m1_subset_1(B_1012,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_1012,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1012,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1012) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_9227])).

tff(c_9575,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6929,c_9569])).

tff(c_9586,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_9575])).

tff(c_9592,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9586,c_68])).

tff(c_10399,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10384,c_9592])).

tff(c_10416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8840,c_10399])).

tff(c_10418,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6940])).

tff(c_10432,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10418,c_8])).

tff(c_6927,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6911,c_149])).

tff(c_6955,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_6927,c_2])).

tff(c_6982,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6955])).

tff(c_10474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10432,c_6982])).

tff(c_10475,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6955])).

tff(c_10478,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10475,c_10475,c_6929])).

tff(c_10481,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10475,c_6911])).

tff(c_11326,plain,(
    ! [A_1153,B_1154,D_1155] :
      ( r2_relset_1(A_1153,B_1154,D_1155,D_1155)
      | ~ m1_subset_1(D_1155,k1_zfmisc_1(k2_zfmisc_1(A_1153,B_1154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11604,plain,(
    ! [D_1192] :
      ( r2_relset_1('#skF_1','#skF_1',D_1192,D_1192)
      | ~ m1_subset_1(D_1192,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10481,c_11326])).

tff(c_11614,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_10478,c_11604])).

tff(c_246,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_234])).

tff(c_259,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_246])).

tff(c_285,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_263])).

tff(c_10540,plain,(
    ! [B_1054,A_1055] :
      ( k2_relat_1(B_1054) = A_1055
      | ~ v2_funct_2(B_1054,A_1055)
      | ~ v5_relat_1(B_1054,A_1055)
      | ~ v1_relat_1(B_1054) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10552,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_10540])).

tff(c_10562,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_10552])).

tff(c_10576,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10562])).

tff(c_74,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_10836,plain,(
    ! [C_1090,B_1091,A_1092] :
      ( v2_funct_2(C_1090,B_1091)
      | ~ v3_funct_2(C_1090,A_1092,B_1091)
      | ~ v1_funct_1(C_1090)
      | ~ m1_subset_1(C_1090,k1_zfmisc_1(k2_zfmisc_1(A_1092,B_1091))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11295,plain,(
    ! [C_1152] :
      ( v2_funct_2(C_1152,'#skF_1')
      | ~ v3_funct_2(C_1152,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1152)
      | ~ m1_subset_1(C_1152,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10481,c_10836])).

tff(c_11301,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10478,c_11295])).

tff(c_11309,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11301])).

tff(c_11311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10576,c_11309])).

tff(c_11312,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10562])).

tff(c_11366,plain,(
    ! [A_1163,B_1164,C_1165] :
      ( k2_relset_1(A_1163,B_1164,C_1165) = k2_relat_1(C_1165)
      | ~ m1_subset_1(C_1165,k1_zfmisc_1(k2_zfmisc_1(A_1163,B_1164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_11845,plain,(
    ! [C_1228] :
      ( k2_relset_1('#skF_1','#skF_1',C_1228) = k2_relat_1(C_1228)
      | ~ m1_subset_1(C_1228,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10481,c_11366])).

tff(c_11851,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10478,c_11845])).

tff(c_11859,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11312,c_11851])).

tff(c_11450,plain,(
    ! [C_1172,A_1173,B_1174] :
      ( v2_funct_1(C_1172)
      | ~ v3_funct_2(C_1172,A_1173,B_1174)
      | ~ v1_funct_1(C_1172)
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(k2_zfmisc_1(A_1173,B_1174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11912,plain,(
    ! [C_1233] :
      ( v2_funct_1(C_1233)
      | ~ v3_funct_2(C_1233,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1233)
      | ~ m1_subset_1(C_1233,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10481,c_11450])).

tff(c_11918,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10478,c_11912])).

tff(c_11926,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11918])).

tff(c_10485,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10475,c_70])).

tff(c_12694,plain,(
    ! [C_1311,D_1312,B_1313,A_1314] :
      ( k2_funct_1(C_1311) = D_1312
      | k1_xboole_0 = B_1313
      | k1_xboole_0 = A_1314
      | ~ v2_funct_1(C_1311)
      | ~ r2_relset_1(A_1314,A_1314,k1_partfun1(A_1314,B_1313,B_1313,A_1314,C_1311,D_1312),k6_partfun1(A_1314))
      | k2_relset_1(A_1314,B_1313,C_1311) != B_1313
      | ~ m1_subset_1(D_1312,k1_zfmisc_1(k2_zfmisc_1(B_1313,A_1314)))
      | ~ v1_funct_2(D_1312,B_1313,A_1314)
      | ~ v1_funct_1(D_1312)
      | ~ m1_subset_1(C_1311,k1_zfmisc_1(k2_zfmisc_1(A_1314,B_1313)))
      | ~ v1_funct_2(C_1311,A_1314,B_1313)
      | ~ v1_funct_1(C_1311) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_12697,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10485,c_12694])).

tff(c_12703,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_10478,c_10481,c_11859,c_11926,c_12697])).

tff(c_12706,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12703])).

tff(c_11324,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10475,c_6940])).

tff(c_11325,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11324])).

tff(c_12733,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12706,c_11325])).

tff(c_12745,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12706,c_12706,c_14])).

tff(c_12967,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12745,c_10481])).

tff(c_12969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12733,c_12967])).

tff(c_12970,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12703])).

tff(c_11865,plain,(
    ! [A_1229,B_1230] :
      ( k2_funct_2(A_1229,B_1230) = k2_funct_1(B_1230)
      | ~ m1_subset_1(B_1230,k1_zfmisc_1(k2_zfmisc_1(A_1229,A_1229)))
      | ~ v3_funct_2(B_1230,A_1229,A_1229)
      | ~ v1_funct_2(B_1230,A_1229,A_1229)
      | ~ v1_funct_1(B_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12234,plain,(
    ! [B_1278] :
      ( k2_funct_2('#skF_1',B_1278) = k2_funct_1(B_1278)
      | ~ m1_subset_1(B_1278,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_1278,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1278,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10481,c_11865])).

tff(c_12240,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10478,c_12234])).

tff(c_12248,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_12240])).

tff(c_48,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_funct_2(A_34,B_35),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v3_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12255,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12248,c_48])).

tff(c_12259,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_10478,c_10481,c_10481,c_12255])).

tff(c_12309,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12259,c_16])).

tff(c_12345,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12309,c_2])).

tff(c_12358,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12345])).

tff(c_12984,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12970,c_12358])).

tff(c_13008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12984])).

tff(c_13009,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12345])).

tff(c_10486,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10475,c_68])).

tff(c_12251,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12248,c_10486])).

tff(c_13013,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13009,c_12251])).

tff(c_13025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11614,c_13013])).

tff(c_13027,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11324])).

tff(c_13026,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11324])).

tff(c_13198,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13027,c_13027,c_13026])).

tff(c_13199,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13198])).

tff(c_13055,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13027,c_8])).

tff(c_13206,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_13055])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13028,plain,(
    ! [A_1324,B_1325,D_1326] :
      ( r2_relset_1(A_1324,B_1325,D_1326,D_1326)
      | ~ m1_subset_1(D_1326,k1_zfmisc_1(k2_zfmisc_1(A_1324,B_1325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_13993,plain,(
    ! [A_1416,B_1417,A_1418] :
      ( r2_relset_1(A_1416,B_1417,A_1418,A_1418)
      | ~ r1_tarski(A_1418,k2_zfmisc_1(A_1416,B_1417)) ) ),
    inference(resolution,[status(thm)],[c_18,c_13028])).

tff(c_14006,plain,(
    ! [A_1416,B_1417] : r2_relset_1(A_1416,B_1417,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13206,c_13993])).

tff(c_13221,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_78])).

tff(c_13219,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_76])).

tff(c_13220,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_74])).

tff(c_13214,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_13199,c_10478])).

tff(c_13054,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13027,c_13027,c_14])).

tff(c_13201,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_13199,c_13054])).

tff(c_13506,plain,(
    ! [A_1354,B_1355] :
      ( k2_funct_2(A_1354,B_1355) = k2_funct_1(B_1355)
      | ~ m1_subset_1(B_1355,k1_zfmisc_1(k2_zfmisc_1(A_1354,A_1354)))
      | ~ v3_funct_2(B_1355,A_1354,A_1354)
      | ~ v1_funct_2(B_1355,A_1354,A_1354)
      | ~ v1_funct_1(B_1355) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14445,plain,(
    ! [B_1498] :
      ( k2_funct_2('#skF_1',B_1498) = k2_funct_1(B_1498)
      | ~ m1_subset_1(B_1498,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_1498,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1498,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1498) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13201,c_13506])).

tff(c_14448,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_13214,c_14445])).

tff(c_14455,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13221,c_13219,c_13220,c_14448])).

tff(c_14466,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14455,c_48])).

tff(c_14472,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13221,c_13219,c_13220,c_13214,c_13201,c_13201,c_14466])).

tff(c_14514,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14472,c_16])).

tff(c_196,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_173])).

tff(c_13047,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13027,c_13027,c_196])).

tff(c_13438,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_13199,c_13047])).

tff(c_14564,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14514,c_13438])).

tff(c_13215,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13199,c_13199,c_10486])).

tff(c_14459,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14455,c_13215])).

tff(c_14574,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14564,c_14459])).

tff(c_14584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14006,c_14574])).

tff(c_14585,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13198])).

tff(c_14586,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13198])).

tff(c_14632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14585,c_14586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.48/3.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.62  
% 9.61/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.62  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.61/3.62  
% 9.61/3.62  %Foreground sorts:
% 9.61/3.62  
% 9.61/3.62  
% 9.61/3.62  %Background operators:
% 9.61/3.62  
% 9.61/3.62  
% 9.61/3.62  %Foreground operators:
% 9.61/3.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.61/3.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.61/3.62  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.61/3.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.61/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.62  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.61/3.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.61/3.62  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.61/3.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.61/3.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.61/3.62  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.61/3.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.61/3.62  tff('#skF_2', type, '#skF_2': $i).
% 9.61/3.62  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.61/3.62  tff('#skF_3', type, '#skF_3': $i).
% 9.61/3.62  tff('#skF_1', type, '#skF_1': $i).
% 9.61/3.62  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.61/3.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.61/3.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.62  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.61/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.61/3.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.61/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.61/3.62  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.61/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.62  
% 9.61/3.66  tff(f_198, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 9.61/3.66  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.61/3.66  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.61/3.66  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.61/3.66  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.61/3.66  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.61/3.66  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.61/3.66  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.61/3.66  tff(f_122, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.61/3.66  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.61/3.66  tff(f_176, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.61/3.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.61/3.66  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.61/3.66  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.61/3.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.61/3.66  tff(f_132, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.61/3.66  tff(f_118, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 9.61/3.66  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_1064, plain, (![A_162, B_163, D_164]: (r2_relset_1(A_162, B_163, D_164, D_164) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.61/3.66  tff(c_1080, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_1064])).
% 9.61/3.66  tff(c_86, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_84, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_80, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.61/3.66  tff(c_234, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.61/3.66  tff(c_249, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_234])).
% 9.61/3.66  tff(c_262, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_249])).
% 9.61/3.66  tff(c_263, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.61/3.66  tff(c_286, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_263])).
% 9.61/3.66  tff(c_442, plain, (![B_99, A_100]: (k2_relat_1(B_99)=A_100 | ~v2_funct_2(B_99, A_100) | ~v5_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.66  tff(c_457, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_286, c_442])).
% 9.61/3.66  tff(c_473, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_457])).
% 9.61/3.66  tff(c_477, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_473])).
% 9.61/3.66  tff(c_82, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_835, plain, (![C_140, B_141, A_142]: (v2_funct_2(C_140, B_141) | ~v3_funct_2(C_140, A_142, B_141) | ~v1_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_848, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_835])).
% 9.61/3.66  tff(c_862, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_848])).
% 9.61/3.66  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_862])).
% 9.61/3.66  tff(c_865, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_473])).
% 9.61/3.66  tff(c_1091, plain, (![A_167, B_168, C_169]: (k2_relset_1(A_167, B_168, C_169)=k2_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.61/3.66  tff(c_1104, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1091])).
% 9.61/3.66  tff(c_1116, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_865, c_1104])).
% 9.61/3.66  tff(c_58, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.61/3.66  tff(c_1078, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_58, c_1064])).
% 9.61/3.66  tff(c_1135, plain, (![C_171, A_172, B_173]: (v2_funct_1(C_171) | ~v3_funct_2(C_171, A_172, B_173) | ~v1_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_1148, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1135])).
% 9.61/3.66  tff(c_1162, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1148])).
% 9.61/3.66  tff(c_1918, plain, (![D_264, A_261, E_260, F_259, B_263, C_262]: (m1_subset_1(k1_partfun1(A_261, B_263, C_262, D_264, E_260, F_259), k1_zfmisc_1(k2_zfmisc_1(A_261, D_264))) | ~m1_subset_1(F_259, k1_zfmisc_1(k2_zfmisc_1(C_262, D_264))) | ~v1_funct_1(F_259) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_263))) | ~v1_funct_1(E_260))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.61/3.66  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_1224, plain, (![D_184, C_185, A_186, B_187]: (D_184=C_185 | ~r2_relset_1(A_186, B_187, C_185, D_184) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.61/3.66  tff(c_1236, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_1224])).
% 9.61/3.66  tff(c_1258, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1236])).
% 9.61/3.66  tff(c_1280, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1258])).
% 9.61/3.66  tff(c_1936, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1918, c_1280])).
% 9.61/3.66  tff(c_1978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_80, c_78, c_72, c_1936])).
% 9.61/3.66  tff(c_1979, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1258])).
% 9.61/3.66  tff(c_3501, plain, (![C_361, D_362, B_363, A_364]: (k2_funct_1(C_361)=D_362 | k1_xboole_0=B_363 | k1_xboole_0=A_364 | ~v2_funct_1(C_361) | ~r2_relset_1(A_364, A_364, k1_partfun1(A_364, B_363, B_363, A_364, C_361, D_362), k6_partfun1(A_364)) | k2_relset_1(A_364, B_363, C_361)!=B_363 | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(B_363, A_364))) | ~v1_funct_2(D_362, B_363, A_364) | ~v1_funct_1(D_362) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_364, B_363))) | ~v1_funct_2(C_361, A_364, B_363) | ~v1_funct_1(C_361))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.61/3.66  tff(c_3504, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1979, c_3501])).
% 9.61/3.66  tff(c_3509, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1116, c_1078, c_1162, c_3504])).
% 9.61/3.66  tff(c_3512, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3509])).
% 9.61/3.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.61/3.66  tff(c_3544, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_8])).
% 9.61/3.66  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.61/3.66  tff(c_3543, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3512, c_14])).
% 9.61/3.66  tff(c_130, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.61/3.66  tff(c_149, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_130])).
% 9.61/3.66  tff(c_173, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.66  tff(c_188, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_149, c_173])).
% 9.61/3.66  tff(c_370, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_188])).
% 9.61/3.66  tff(c_3691, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3543, c_370])).
% 9.61/3.66  tff(c_3699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3544, c_3691])).
% 9.61/3.66  tff(c_3700, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_3509])).
% 9.61/3.66  tff(c_2125, plain, (![A_282, B_283]: (k2_funct_2(A_282, B_283)=k2_funct_1(B_283) | ~m1_subset_1(B_283, k1_zfmisc_1(k2_zfmisc_1(A_282, A_282))) | ~v3_funct_2(B_283, A_282, A_282) | ~v1_funct_2(B_283, A_282, A_282) | ~v1_funct_1(B_283))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.66  tff(c_2138, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_2125])).
% 9.61/3.66  tff(c_2154, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_2138])).
% 9.61/3.66  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_2161, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_68])).
% 9.61/3.66  tff(c_3758, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3700, c_2161])).
% 9.61/3.66  tff(c_3777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1080, c_3758])).
% 9.61/3.66  tff(c_3778, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 9.61/3.66  tff(c_3783, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3778, c_72])).
% 9.61/3.66  tff(c_3848, plain, (![A_375, B_376, D_377]: (r2_relset_1(A_375, B_376, D_377, D_377) | ~m1_subset_1(D_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.61/3.66  tff(c_5189, plain, (![D_530]: (r2_relset_1('#skF_1', '#skF_1', D_530, D_530) | ~m1_subset_1(D_530, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3778, c_3848])).
% 9.61/3.66  tff(c_5202, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3783, c_5189])).
% 9.61/3.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.66  tff(c_3784, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3778, c_80])).
% 9.61/3.66  tff(c_3896, plain, (![B_383, A_384]: (k2_relat_1(B_383)=A_384 | ~v2_funct_2(B_383, A_384) | ~v5_relat_1(B_383, A_384) | ~v1_relat_1(B_383))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.66  tff(c_3911, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_286, c_3896])).
% 9.61/3.66  tff(c_3925, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_3911])).
% 9.61/3.66  tff(c_3929, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_3925])).
% 9.61/3.66  tff(c_4186, plain, (![C_416, B_417, A_418]: (v2_funct_2(C_416, B_417) | ~v3_funct_2(C_416, A_418, B_417) | ~v1_funct_1(C_416) | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(A_418, B_417))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_4465, plain, (![C_450]: (v2_funct_2(C_450, '#skF_1') | ~v3_funct_2(C_450, '#skF_1', '#skF_1') | ~v1_funct_1(C_450) | ~m1_subset_1(C_450, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3778, c_4186])).
% 9.61/3.66  tff(c_4471, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_3784, c_4465])).
% 9.61/3.66  tff(c_4482, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_4471])).
% 9.61/3.66  tff(c_4484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3929, c_4482])).
% 9.61/3.66  tff(c_4485, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_3925])).
% 9.61/3.66  tff(c_5147, plain, (![A_525, B_526, C_527]: (k2_relset_1(A_525, B_526, C_527)=k2_relat_1(C_527) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.61/3.66  tff(c_5320, plain, (![C_545]: (k2_relset_1('#skF_1', '#skF_1', C_545)=k2_relat_1(C_545) | ~m1_subset_1(C_545, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3778, c_5147])).
% 9.61/3.66  tff(c_5326, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3784, c_5320])).
% 9.61/3.66  tff(c_5337, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4485, c_5326])).
% 9.61/3.66  tff(c_5243, plain, (![C_536, A_537, B_538]: (v2_funct_1(C_536) | ~v3_funct_2(C_536, A_537, B_538) | ~v1_funct_1(C_536) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_5389, plain, (![C_556]: (v2_funct_1(C_556) | ~v3_funct_2(C_556, '#skF_1', '#skF_1') | ~v1_funct_1(C_556) | ~m1_subset_1(C_556, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3778, c_5243])).
% 9.61/3.66  tff(c_5395, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_3784, c_5389])).
% 9.61/3.66  tff(c_5406, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_5395])).
% 9.61/3.66  tff(c_6561, plain, (![C_671, D_672, B_673, A_674]: (k2_funct_1(C_671)=D_672 | k1_xboole_0=B_673 | k1_xboole_0=A_674 | ~v2_funct_1(C_671) | ~r2_relset_1(A_674, A_674, k1_partfun1(A_674, B_673, B_673, A_674, C_671, D_672), k6_partfun1(A_674)) | k2_relset_1(A_674, B_673, C_671)!=B_673 | ~m1_subset_1(D_672, k1_zfmisc_1(k2_zfmisc_1(B_673, A_674))) | ~v1_funct_2(D_672, B_673, A_674) | ~v1_funct_1(D_672) | ~m1_subset_1(C_671, k1_zfmisc_1(k2_zfmisc_1(A_674, B_673))) | ~v1_funct_2(C_671, A_674, B_673) | ~v1_funct_1(C_671))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.61/3.66  tff(c_6564, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_6561])).
% 9.61/3.66  tff(c_6570, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_3784, c_3778, c_78, c_76, c_3783, c_3778, c_5337, c_5406, c_6564])).
% 9.61/3.66  tff(c_6573, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6570])).
% 9.61/3.66  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.61/3.66  tff(c_3795, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3778, c_10])).
% 9.61/3.66  tff(c_3863, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3795])).
% 9.61/3.66  tff(c_6597, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6573, c_3863])).
% 9.61/3.66  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.61/3.66  tff(c_6610, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6573, c_6573, c_12])).
% 9.61/3.66  tff(c_6780, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6610, c_3778])).
% 9.61/3.66  tff(c_6782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6597, c_6780])).
% 9.61/3.66  tff(c_6783, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_6570])).
% 9.61/3.66  tff(c_5679, plain, (![A_590, B_591]: (k2_funct_2(A_590, B_591)=k2_funct_1(B_591) | ~m1_subset_1(B_591, k1_zfmisc_1(k2_zfmisc_1(A_590, A_590))) | ~v3_funct_2(B_591, A_590, A_590) | ~v1_funct_2(B_591, A_590, A_590) | ~v1_funct_1(B_591))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.66  tff(c_5951, plain, (![B_623]: (k2_funct_2('#skF_1', B_623)=k2_funct_1(B_623) | ~m1_subset_1(B_623, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_623, '#skF_1', '#skF_1') | ~v1_funct_2(B_623, '#skF_1', '#skF_1') | ~v1_funct_1(B_623))), inference(superposition, [status(thm), theory('equality')], [c_3778, c_5679])).
% 9.61/3.66  tff(c_5957, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_3784, c_5951])).
% 9.61/3.66  tff(c_5968, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_5957])).
% 9.61/3.66  tff(c_6051, plain, (![A_644, B_645]: (m1_subset_1(k2_funct_2(A_644, B_645), k1_zfmisc_1(k2_zfmisc_1(A_644, A_644))) | ~m1_subset_1(B_645, k1_zfmisc_1(k2_zfmisc_1(A_644, A_644))) | ~v3_funct_2(B_645, A_644, A_644) | ~v1_funct_2(B_645, A_644, A_644) | ~v1_funct_1(B_645))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.61/3.66  tff(c_6092, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5968, c_6051])).
% 9.61/3.66  tff(c_6122, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_3784, c_3778, c_3778, c_6092])).
% 9.61/3.66  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.61/3.66  tff(c_6261, plain, (r1_tarski(k2_funct_1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_6122, c_16])).
% 9.61/3.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.66  tff(c_6346, plain, (k2_funct_1('#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6261, c_2])).
% 9.61/3.66  tff(c_6502, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_6346])).
% 9.61/3.66  tff(c_6786, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6783, c_6502])).
% 9.61/3.66  tff(c_6804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6786])).
% 9.61/3.66  tff(c_6805, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_6346])).
% 9.61/3.66  tff(c_5974, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_68])).
% 9.61/3.66  tff(c_6845, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6805, c_5974])).
% 9.61/3.66  tff(c_6861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5202, c_6845])).
% 9.61/3.66  tff(c_6863, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3795])).
% 9.61/3.66  tff(c_6879, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6863, c_8])).
% 9.61/3.66  tff(c_150, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_130])).
% 9.61/3.66  tff(c_187, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_150, c_173])).
% 9.61/3.66  tff(c_334, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_187])).
% 9.61/3.66  tff(c_3780, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3778, c_334])).
% 9.61/3.66  tff(c_6910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6879, c_3780])).
% 9.61/3.66  tff(c_6911, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_187])).
% 9.61/3.66  tff(c_6928, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6911, c_72])).
% 9.61/3.66  tff(c_8615, plain, (![A_881, B_882, D_883]: (r2_relset_1(A_881, B_882, D_883, D_883) | ~m1_subset_1(D_883, k1_zfmisc_1(k2_zfmisc_1(A_881, B_882))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.61/3.66  tff(c_8827, plain, (![D_909]: (r2_relset_1('#skF_1', '#skF_1', D_909, D_909) | ~m1_subset_1(D_909, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6911, c_8615])).
% 9.61/3.66  tff(c_8840, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_6928, c_8827])).
% 9.61/3.66  tff(c_6929, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6911, c_80])).
% 9.61/3.66  tff(c_6983, plain, (![B_685, A_686]: (k2_relat_1(B_685)=A_686 | ~v2_funct_2(B_685, A_686) | ~v5_relat_1(B_685, A_686) | ~v1_relat_1(B_685))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.66  tff(c_6995, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_286, c_6983])).
% 9.61/3.66  tff(c_7008, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_6995])).
% 9.61/3.66  tff(c_7023, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_7008])).
% 9.61/3.66  tff(c_7317, plain, (![C_725, B_726, A_727]: (v2_funct_2(C_725, B_726) | ~v3_funct_2(C_725, A_727, B_726) | ~v1_funct_1(C_725) | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_727, B_726))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_7796, plain, (![C_786]: (v2_funct_2(C_786, '#skF_1') | ~v3_funct_2(C_786, '#skF_1', '#skF_1') | ~v1_funct_1(C_786) | ~m1_subset_1(C_786, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6911, c_7317])).
% 9.61/3.66  tff(c_7802, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6929, c_7796])).
% 9.61/3.66  tff(c_7813, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7802])).
% 9.61/3.66  tff(c_7815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7023, c_7813])).
% 9.61/3.66  tff(c_7816, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_7008])).
% 9.61/3.66  tff(c_8668, plain, (![A_893, B_894, C_895]: (k2_relset_1(A_893, B_894, C_895)=k2_relat_1(C_895) | ~m1_subset_1(C_895, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.61/3.66  tff(c_8933, plain, (![C_924]: (k2_relset_1('#skF_1', '#skF_1', C_924)=k2_relat_1(C_924) | ~m1_subset_1(C_924, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6911, c_8668])).
% 9.61/3.66  tff(c_8939, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6929, c_8933])).
% 9.61/3.66  tff(c_8950, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7816, c_8939])).
% 9.61/3.66  tff(c_8765, plain, (![C_902, A_903, B_904]: (v2_funct_1(C_902) | ~v3_funct_2(C_902, A_903, B_904) | ~v1_funct_1(C_902) | ~m1_subset_1(C_902, k1_zfmisc_1(k2_zfmisc_1(A_903, B_904))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_9254, plain, (![C_963]: (v2_funct_1(C_963) | ~v3_funct_2(C_963, '#skF_1', '#skF_1') | ~v1_funct_1(C_963) | ~m1_subset_1(C_963, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6911, c_8765])).
% 9.61/3.66  tff(c_9260, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6929, c_9254])).
% 9.61/3.66  tff(c_9271, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_9260])).
% 9.61/3.66  tff(c_10094, plain, (![C_1038, D_1039, B_1040, A_1041]: (k2_funct_1(C_1038)=D_1039 | k1_xboole_0=B_1040 | k1_xboole_0=A_1041 | ~v2_funct_1(C_1038) | ~r2_relset_1(A_1041, A_1041, k1_partfun1(A_1041, B_1040, B_1040, A_1041, C_1038, D_1039), k6_partfun1(A_1041)) | k2_relset_1(A_1041, B_1040, C_1038)!=B_1040 | ~m1_subset_1(D_1039, k1_zfmisc_1(k2_zfmisc_1(B_1040, A_1041))) | ~v1_funct_2(D_1039, B_1040, A_1041) | ~v1_funct_1(D_1039) | ~m1_subset_1(C_1038, k1_zfmisc_1(k2_zfmisc_1(A_1041, B_1040))) | ~v1_funct_2(C_1038, A_1041, B_1040) | ~v1_funct_1(C_1038))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.61/3.66  tff(c_10097, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_10094])).
% 9.61/3.66  tff(c_10103, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_6929, c_6911, c_78, c_76, c_6928, c_6911, c_8950, c_9271, c_10097])).
% 9.61/3.66  tff(c_10106, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_10103])).
% 9.61/3.66  tff(c_6940, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6911, c_10])).
% 9.61/3.66  tff(c_8614, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_6940])).
% 9.61/3.66  tff(c_10133, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10106, c_8614])).
% 9.61/3.66  tff(c_10143, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10106, c_10106, c_12])).
% 9.61/3.66  tff(c_10381, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10143, c_6911])).
% 9.61/3.66  tff(c_10383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10133, c_10381])).
% 9.61/3.66  tff(c_10384, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_10103])).
% 9.61/3.66  tff(c_9227, plain, (![A_960, B_961]: (k2_funct_2(A_960, B_961)=k2_funct_1(B_961) | ~m1_subset_1(B_961, k1_zfmisc_1(k2_zfmisc_1(A_960, A_960))) | ~v3_funct_2(B_961, A_960, A_960) | ~v1_funct_2(B_961, A_960, A_960) | ~v1_funct_1(B_961))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.66  tff(c_9569, plain, (![B_1012]: (k2_funct_2('#skF_1', B_1012)=k2_funct_1(B_1012) | ~m1_subset_1(B_1012, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_1012, '#skF_1', '#skF_1') | ~v1_funct_2(B_1012, '#skF_1', '#skF_1') | ~v1_funct_1(B_1012))), inference(superposition, [status(thm), theory('equality')], [c_6911, c_9227])).
% 9.61/3.66  tff(c_9575, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6929, c_9569])).
% 9.61/3.66  tff(c_9586, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_9575])).
% 9.61/3.66  tff(c_9592, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9586, c_68])).
% 9.61/3.66  tff(c_10399, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10384, c_9592])).
% 9.61/3.66  tff(c_10416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8840, c_10399])).
% 9.61/3.66  tff(c_10418, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_6940])).
% 9.61/3.66  tff(c_10432, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10418, c_8])).
% 9.61/3.66  tff(c_6927, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6911, c_149])).
% 9.61/3.66  tff(c_6955, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_6927, c_2])).
% 9.61/3.66  tff(c_6982, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_6955])).
% 9.61/3.66  tff(c_10474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10432, c_6982])).
% 9.61/3.66  tff(c_10475, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_6955])).
% 9.61/3.66  tff(c_10478, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10475, c_10475, c_6929])).
% 9.61/3.66  tff(c_10481, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10475, c_6911])).
% 9.61/3.66  tff(c_11326, plain, (![A_1153, B_1154, D_1155]: (r2_relset_1(A_1153, B_1154, D_1155, D_1155) | ~m1_subset_1(D_1155, k1_zfmisc_1(k2_zfmisc_1(A_1153, B_1154))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.61/3.66  tff(c_11604, plain, (![D_1192]: (r2_relset_1('#skF_1', '#skF_1', D_1192, D_1192) | ~m1_subset_1(D_1192, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10481, c_11326])).
% 9.61/3.66  tff(c_11614, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_10478, c_11604])).
% 9.61/3.66  tff(c_246, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_234])).
% 9.61/3.66  tff(c_259, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_246])).
% 9.61/3.66  tff(c_285, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_263])).
% 9.61/3.66  tff(c_10540, plain, (![B_1054, A_1055]: (k2_relat_1(B_1054)=A_1055 | ~v2_funct_2(B_1054, A_1055) | ~v5_relat_1(B_1054, A_1055) | ~v1_relat_1(B_1054))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.66  tff(c_10552, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_10540])).
% 9.61/3.66  tff(c_10562, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_10552])).
% 9.61/3.66  tff(c_10576, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_10562])).
% 9.61/3.66  tff(c_74, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.61/3.66  tff(c_10836, plain, (![C_1090, B_1091, A_1092]: (v2_funct_2(C_1090, B_1091) | ~v3_funct_2(C_1090, A_1092, B_1091) | ~v1_funct_1(C_1090) | ~m1_subset_1(C_1090, k1_zfmisc_1(k2_zfmisc_1(A_1092, B_1091))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_11295, plain, (![C_1152]: (v2_funct_2(C_1152, '#skF_1') | ~v3_funct_2(C_1152, '#skF_1', '#skF_1') | ~v1_funct_1(C_1152) | ~m1_subset_1(C_1152, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10481, c_10836])).
% 9.61/3.66  tff(c_11301, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10478, c_11295])).
% 9.61/3.66  tff(c_11309, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11301])).
% 9.61/3.66  tff(c_11311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10576, c_11309])).
% 9.61/3.66  tff(c_11312, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_10562])).
% 9.61/3.66  tff(c_11366, plain, (![A_1163, B_1164, C_1165]: (k2_relset_1(A_1163, B_1164, C_1165)=k2_relat_1(C_1165) | ~m1_subset_1(C_1165, k1_zfmisc_1(k2_zfmisc_1(A_1163, B_1164))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.61/3.66  tff(c_11845, plain, (![C_1228]: (k2_relset_1('#skF_1', '#skF_1', C_1228)=k2_relat_1(C_1228) | ~m1_subset_1(C_1228, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10481, c_11366])).
% 9.61/3.66  tff(c_11851, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10478, c_11845])).
% 9.61/3.66  tff(c_11859, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11312, c_11851])).
% 9.61/3.66  tff(c_11450, plain, (![C_1172, A_1173, B_1174]: (v2_funct_1(C_1172) | ~v3_funct_2(C_1172, A_1173, B_1174) | ~v1_funct_1(C_1172) | ~m1_subset_1(C_1172, k1_zfmisc_1(k2_zfmisc_1(A_1173, B_1174))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.66  tff(c_11912, plain, (![C_1233]: (v2_funct_1(C_1233) | ~v3_funct_2(C_1233, '#skF_1', '#skF_1') | ~v1_funct_1(C_1233) | ~m1_subset_1(C_1233, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10481, c_11450])).
% 9.61/3.66  tff(c_11918, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10478, c_11912])).
% 9.61/3.66  tff(c_11926, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11918])).
% 9.61/3.66  tff(c_10485, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10475, c_70])).
% 9.61/3.66  tff(c_12694, plain, (![C_1311, D_1312, B_1313, A_1314]: (k2_funct_1(C_1311)=D_1312 | k1_xboole_0=B_1313 | k1_xboole_0=A_1314 | ~v2_funct_1(C_1311) | ~r2_relset_1(A_1314, A_1314, k1_partfun1(A_1314, B_1313, B_1313, A_1314, C_1311, D_1312), k6_partfun1(A_1314)) | k2_relset_1(A_1314, B_1313, C_1311)!=B_1313 | ~m1_subset_1(D_1312, k1_zfmisc_1(k2_zfmisc_1(B_1313, A_1314))) | ~v1_funct_2(D_1312, B_1313, A_1314) | ~v1_funct_1(D_1312) | ~m1_subset_1(C_1311, k1_zfmisc_1(k2_zfmisc_1(A_1314, B_1313))) | ~v1_funct_2(C_1311, A_1314, B_1313) | ~v1_funct_1(C_1311))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.61/3.66  tff(c_12697, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10485, c_12694])).
% 9.61/3.66  tff(c_12703, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_10478, c_10481, c_11859, c_11926, c_12697])).
% 9.61/3.66  tff(c_12706, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12703])).
% 9.61/3.66  tff(c_11324, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10475, c_6940])).
% 9.61/3.66  tff(c_11325, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_11324])).
% 9.61/3.66  tff(c_12733, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12706, c_11325])).
% 9.61/3.66  tff(c_12745, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12706, c_12706, c_14])).
% 9.61/3.66  tff(c_12967, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12745, c_10481])).
% 9.61/3.66  tff(c_12969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12733, c_12967])).
% 9.61/3.66  tff(c_12970, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_12703])).
% 9.61/3.66  tff(c_11865, plain, (![A_1229, B_1230]: (k2_funct_2(A_1229, B_1230)=k2_funct_1(B_1230) | ~m1_subset_1(B_1230, k1_zfmisc_1(k2_zfmisc_1(A_1229, A_1229))) | ~v3_funct_2(B_1230, A_1229, A_1229) | ~v1_funct_2(B_1230, A_1229, A_1229) | ~v1_funct_1(B_1230))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.66  tff(c_12234, plain, (![B_1278]: (k2_funct_2('#skF_1', B_1278)=k2_funct_1(B_1278) | ~m1_subset_1(B_1278, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_1278, '#skF_1', '#skF_1') | ~v1_funct_2(B_1278, '#skF_1', '#skF_1') | ~v1_funct_1(B_1278))), inference(superposition, [status(thm), theory('equality')], [c_10481, c_11865])).
% 9.61/3.66  tff(c_12240, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10478, c_12234])).
% 9.61/3.66  tff(c_12248, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_12240])).
% 9.61/3.66  tff(c_48, plain, (![A_34, B_35]: (m1_subset_1(k2_funct_2(A_34, B_35), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~v3_funct_2(B_35, A_34, A_34) | ~v1_funct_2(B_35, A_34, A_34) | ~v1_funct_1(B_35))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.61/3.66  tff(c_12255, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12248, c_48])).
% 9.61/3.66  tff(c_12259, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_10478, c_10481, c_10481, c_12255])).
% 9.61/3.66  tff(c_12309, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_12259, c_16])).
% 9.61/3.66  tff(c_12345, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12309, c_2])).
% 9.61/3.66  tff(c_12358, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12345])).
% 9.61/3.66  tff(c_12984, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12970, c_12358])).
% 9.61/3.66  tff(c_13008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12984])).
% 9.61/3.66  tff(c_13009, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_12345])).
% 9.61/3.66  tff(c_10486, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10475, c_68])).
% 9.61/3.66  tff(c_12251, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12248, c_10486])).
% 9.61/3.66  tff(c_13013, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13009, c_12251])).
% 9.61/3.66  tff(c_13025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11614, c_13013])).
% 9.61/3.66  tff(c_13027, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_11324])).
% 9.61/3.66  tff(c_13026, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_11324])).
% 9.61/3.66  tff(c_13198, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13027, c_13027, c_13026])).
% 9.61/3.66  tff(c_13199, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_13198])).
% 9.61/3.66  tff(c_13055, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13027, c_8])).
% 9.61/3.66  tff(c_13206, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_13055])).
% 9.61/3.66  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.61/3.66  tff(c_13028, plain, (![A_1324, B_1325, D_1326]: (r2_relset_1(A_1324, B_1325, D_1326, D_1326) | ~m1_subset_1(D_1326, k1_zfmisc_1(k2_zfmisc_1(A_1324, B_1325))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.61/3.66  tff(c_13993, plain, (![A_1416, B_1417, A_1418]: (r2_relset_1(A_1416, B_1417, A_1418, A_1418) | ~r1_tarski(A_1418, k2_zfmisc_1(A_1416, B_1417)))), inference(resolution, [status(thm)], [c_18, c_13028])).
% 9.61/3.66  tff(c_14006, plain, (![A_1416, B_1417]: (r2_relset_1(A_1416, B_1417, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_13206, c_13993])).
% 9.61/3.66  tff(c_13221, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_78])).
% 9.61/3.66  tff(c_13219, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_76])).
% 9.61/3.66  tff(c_13220, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_74])).
% 9.61/3.66  tff(c_13214, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_13199, c_10478])).
% 9.61/3.66  tff(c_13054, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13027, c_13027, c_14])).
% 9.61/3.66  tff(c_13201, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_13199, c_13054])).
% 9.61/3.66  tff(c_13506, plain, (![A_1354, B_1355]: (k2_funct_2(A_1354, B_1355)=k2_funct_1(B_1355) | ~m1_subset_1(B_1355, k1_zfmisc_1(k2_zfmisc_1(A_1354, A_1354))) | ~v3_funct_2(B_1355, A_1354, A_1354) | ~v1_funct_2(B_1355, A_1354, A_1354) | ~v1_funct_1(B_1355))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.61/3.66  tff(c_14445, plain, (![B_1498]: (k2_funct_2('#skF_1', B_1498)=k2_funct_1(B_1498) | ~m1_subset_1(B_1498, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_1498, '#skF_1', '#skF_1') | ~v1_funct_2(B_1498, '#skF_1', '#skF_1') | ~v1_funct_1(B_1498))), inference(superposition, [status(thm), theory('equality')], [c_13201, c_13506])).
% 9.61/3.66  tff(c_14448, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_13214, c_14445])).
% 9.61/3.66  tff(c_14455, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13221, c_13219, c_13220, c_14448])).
% 9.61/3.66  tff(c_14466, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14455, c_48])).
% 9.61/3.66  tff(c_14472, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13221, c_13219, c_13220, c_13214, c_13201, c_13201, c_14466])).
% 9.61/3.66  tff(c_14514, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_14472, c_16])).
% 9.61/3.66  tff(c_196, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_173])).
% 9.61/3.66  tff(c_13047, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13027, c_13027, c_196])).
% 9.61/3.66  tff(c_13438, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_13199, c_13047])).
% 9.61/3.66  tff(c_14564, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_14514, c_13438])).
% 9.61/3.66  tff(c_13215, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13199, c_13199, c_10486])).
% 9.61/3.66  tff(c_14459, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14455, c_13215])).
% 9.61/3.66  tff(c_14574, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14564, c_14459])).
% 9.61/3.66  tff(c_14584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14006, c_14574])).
% 9.61/3.66  tff(c_14585, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_13198])).
% 9.61/3.66  tff(c_14586, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_13198])).
% 9.61/3.66  tff(c_14632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14585, c_14586])).
% 9.61/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.66  
% 9.61/3.66  Inference rules
% 9.61/3.66  ----------------------
% 9.61/3.66  #Ref     : 0
% 9.61/3.66  #Sup     : 3107
% 9.61/3.66  #Fact    : 0
% 9.61/3.66  #Define  : 0
% 9.61/3.66  #Split   : 60
% 9.61/3.66  #Chain   : 0
% 9.61/3.66  #Close   : 0
% 9.61/3.66  
% 9.61/3.66  Ordering : KBO
% 9.61/3.66  
% 9.61/3.66  Simplification rules
% 9.61/3.66  ----------------------
% 9.61/3.66  #Subsume      : 310
% 9.61/3.66  #Demod        : 3368
% 9.61/3.66  #Tautology    : 1427
% 9.61/3.66  #SimpNegUnit  : 16
% 9.61/3.66  #BackRed      : 476
% 9.61/3.66  
% 9.61/3.66  #Partial instantiations: 0
% 9.61/3.66  #Strategies tried      : 1
% 9.61/3.66  
% 9.61/3.66  Timing (in seconds)
% 9.61/3.66  ----------------------
% 9.61/3.66  Preprocessing        : 0.36
% 9.61/3.66  Parsing              : 0.19
% 9.61/3.66  CNF conversion       : 0.03
% 9.61/3.66  Main loop            : 2.44
% 9.61/3.66  Inferencing          : 0.80
% 9.61/3.66  Reduction            : 0.93
% 9.61/3.66  Demodulation         : 0.68
% 9.61/3.66  BG Simplification    : 0.07
% 9.61/3.66  Subsumption          : 0.44
% 9.61/3.66  Abstraction          : 0.08
% 9.61/3.66  MUC search           : 0.00
% 9.61/3.66  Cooper               : 0.00
% 9.61/3.66  Total                : 2.90
% 9.61/3.66  Index Insertion      : 0.00
% 9.61/3.66  Index Deletion       : 0.00
% 9.61/3.66  Index Matching       : 0.00
% 9.61/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
