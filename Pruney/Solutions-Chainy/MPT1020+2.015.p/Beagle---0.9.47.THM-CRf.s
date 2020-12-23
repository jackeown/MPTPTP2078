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
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 842 expanded)
%              Number of leaves         :   42 ( 294 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 (2438 expanded)
%              Number of equality atoms :   48 ( 275 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_169,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_111,axiom,(
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

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_182,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_190,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_182])).

tff(c_128,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_xboole_0(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_128])).

tff(c_141,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_85,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_85])).

tff(c_98,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_98])).

tff(c_257,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(B_74) = A_75
      | ~ v2_funct_2(B_74,A_75)
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_266,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_257])).

tff(c_278,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_266])).

tff(c_282,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_527,plain,(
    ! [C_101,B_102,A_103] :
      ( v2_funct_2(C_101,B_102)
      | ~ v3_funct_2(C_101,A_103,B_102)
      | ~ v1_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_539,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_527])).

tff(c_547,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_539])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_547])).

tff(c_550,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_682,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_694,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_682])).

tff(c_700,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_694])).

tff(c_44,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_189,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_745,plain,(
    ! [C_122,A_123,B_124] :
      ( v2_funct_1(C_122)
      | ~ v3_funct_2(C_122,A_123,B_124)
      | ~ v1_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_757,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_745])).

tff(c_765,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_757])).

tff(c_2299,plain,(
    ! [D_184,B_188,A_185,E_189,F_187,C_186] :
      ( m1_subset_1(k1_partfun1(A_185,B_188,C_186,D_184,E_189,F_187),k1_zfmisc_1(k2_zfmisc_1(A_185,D_184)))
      | ~ m1_subset_1(F_187,k1_zfmisc_1(k2_zfmisc_1(C_186,D_184)))
      | ~ v1_funct_1(F_187)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_185,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_830,plain,(
    ! [D_132,C_133,A_134,B_135] :
      ( D_132 = C_133
      | ~ r2_relset_1(A_134,B_135,C_133,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_840,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_830])).

tff(c_859,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_840])).

tff(c_877,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_2317,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2299,c_877])).

tff(c_2353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_64,c_58,c_2317])).

tff(c_2354,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_3549,plain,(
    ! [C_246,D_247,B_248,A_249] :
      ( k2_funct_1(C_246) = D_247
      | k1_xboole_0 = B_248
      | k1_xboole_0 = A_249
      | ~ v2_funct_1(C_246)
      | ~ r2_relset_1(A_249,A_249,k1_partfun1(A_249,B_248,B_248,A_249,C_246,D_247),k6_partfun1(A_249))
      | k2_relset_1(A_249,B_248,C_246) != B_248
      | ~ m1_subset_1(D_247,k1_zfmisc_1(k2_zfmisc_1(B_248,A_249)))
      | ~ v1_funct_2(D_247,B_248,A_249)
      | ~ v1_funct_1(D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_2(C_246,A_249,B_248)
      | ~ v1_funct_1(C_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_3558,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_3549])).

tff(c_3566,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_700,c_189,c_765,c_3558])).

tff(c_3568,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3566])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3593,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3568,c_2])).

tff(c_3595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_3593])).

tff(c_3596,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3566])).

tff(c_2707,plain,(
    ! [A_200,B_201] :
      ( k2_funct_2(A_200,B_201) = k2_funct_1(B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ v3_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2722,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2707])).

tff(c_2731,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2722])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2738,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_54])).

tff(c_3657,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3596,c_2738])).

tff(c_3679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_3657])).

tff(c_3681,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_140,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_128])).

tff(c_3734,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3681,c_140])).

tff(c_74,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | B_48 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_3694,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3681,c_77])).

tff(c_3680,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_3687,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3680,c_77])).

tff(c_3713,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3694,c_3687])).

tff(c_3696,plain,(
    ! [A_49] :
      ( A_49 = '#skF_3'
      | ~ v1_xboole_0(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3687,c_77])).

tff(c_3739,plain,(
    ! [A_255] :
      ( A_255 = '#skF_1'
      | ~ v1_xboole_0(A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_3696])).

tff(c_3746,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3734,c_3739])).

tff(c_3703,plain,(
    ! [A_252,B_253,D_254] :
      ( r2_relset_1(A_252,B_253,D_254,D_254)
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3712,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3703])).

tff(c_3791,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_3746,c_3712])).

tff(c_3727,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_64])).

tff(c_3725,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_62])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3726,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_60])).

tff(c_3724,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_58])).

tff(c_4790,plain,(
    ! [A_317,B_318] :
      ( k2_funct_2(A_317,B_318) = k2_funct_1(B_318)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(k2_zfmisc_1(A_317,A_317)))
      | ~ v3_funct_2(B_318,A_317,A_317)
      | ~ v1_funct_2(B_318,A_317,A_317)
      | ~ v1_funct_1(B_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4796,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3724,c_4790])).

tff(c_4805,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3727,c_3725,c_3726,c_4796])).

tff(c_6989,plain,(
    ! [A_361,B_362] :
      ( m1_subset_1(k2_funct_2(A_361,B_362),k1_zfmisc_1(k2_zfmisc_1(A_361,A_361)))
      | ~ m1_subset_1(B_362,k1_zfmisc_1(k2_zfmisc_1(A_361,A_361)))
      | ~ v3_funct_2(B_362,A_361,A_361)
      | ~ v1_funct_2(B_362,A_361,A_361)
      | ~ v1_funct_1(B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7030,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4805,c_6989])).

tff(c_7046,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3727,c_3725,c_3726,c_3724,c_7030])).

tff(c_12,plain,(
    ! [C_12,A_9,B_10] :
      ( v1_xboole_0(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7075,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7046,c_12])).

tff(c_7113,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3681,c_7075])).

tff(c_3738,plain,(
    ! [A_49] :
      ( A_49 = '#skF_1'
      | ~ v1_xboole_0(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_3696])).

tff(c_7144,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7113,c_3738])).

tff(c_3723,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_54])).

tff(c_4004,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_3723])).

tff(c_4808,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4805,c_4004])).

tff(c_7179,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7144,c_4808])).

tff(c_7190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3791,c_7179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:37:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.70/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.36  
% 6.70/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.36  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.70/2.36  
% 6.70/2.36  %Foreground sorts:
% 6.70/2.36  
% 6.70/2.36  
% 6.70/2.36  %Background operators:
% 6.70/2.36  
% 6.70/2.36  
% 6.70/2.36  %Foreground operators:
% 6.70/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.70/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.70/2.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.70/2.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.70/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.70/2.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.70/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.70/2.36  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.70/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.70/2.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.70/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.70/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.70/2.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.70/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.70/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.70/2.36  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.70/2.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.70/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.70/2.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.70/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.70/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.70/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.70/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.70/2.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.70/2.36  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.70/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.70/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.70/2.36  
% 7.09/2.38  tff(f_191, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 7.09/2.38  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.09/2.38  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.09/2.38  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.09/2.38  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.09/2.38  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.09/2.38  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.09/2.38  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.09/2.38  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.09/2.38  tff(f_95, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.09/2.38  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.09/2.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.09/2.38  tff(f_125, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.09/2.38  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 7.09/2.38  tff(f_111, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.09/2.38  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_182, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.09/2.38  tff(c_190, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_182])).
% 7.09/2.38  tff(c_128, plain, (![C_65, A_66, B_67]: (v1_xboole_0(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.09/2.38  tff(c_139, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_128])).
% 7.09/2.38  tff(c_141, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_139])).
% 7.09/2.38  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_85, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.09/2.38  tff(c_97, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_85])).
% 7.09/2.38  tff(c_98, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.09/2.38  tff(c_110, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_98])).
% 7.09/2.38  tff(c_257, plain, (![B_74, A_75]: (k2_relat_1(B_74)=A_75 | ~v2_funct_2(B_74, A_75) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.09/2.38  tff(c_266, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_110, c_257])).
% 7.09/2.38  tff(c_278, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_266])).
% 7.09/2.38  tff(c_282, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_278])).
% 7.09/2.38  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_527, plain, (![C_101, B_102, A_103]: (v2_funct_2(C_101, B_102) | ~v3_funct_2(C_101, A_103, B_102) | ~v1_funct_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.09/2.38  tff(c_539, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_527])).
% 7.09/2.38  tff(c_547, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_539])).
% 7.09/2.38  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_547])).
% 7.09/2.38  tff(c_550, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_278])).
% 7.09/2.38  tff(c_682, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.09/2.38  tff(c_694, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_682])).
% 7.09/2.38  tff(c_700, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_550, c_694])).
% 7.09/2.38  tff(c_44, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.09/2.38  tff(c_189, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_44, c_182])).
% 7.09/2.38  tff(c_745, plain, (![C_122, A_123, B_124]: (v2_funct_1(C_122) | ~v3_funct_2(C_122, A_123, B_124) | ~v1_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.09/2.38  tff(c_757, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_745])).
% 7.09/2.38  tff(c_765, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_757])).
% 7.09/2.38  tff(c_2299, plain, (![D_184, B_188, A_185, E_189, F_187, C_186]: (m1_subset_1(k1_partfun1(A_185, B_188, C_186, D_184, E_189, F_187), k1_zfmisc_1(k2_zfmisc_1(A_185, D_184))) | ~m1_subset_1(F_187, k1_zfmisc_1(k2_zfmisc_1(C_186, D_184))) | ~v1_funct_1(F_187) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_185, B_188))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.09/2.38  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_830, plain, (![D_132, C_133, A_134, B_135]: (D_132=C_133 | ~r2_relset_1(A_134, B_135, C_133, D_132) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.09/2.38  tff(c_840, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_830])).
% 7.09/2.38  tff(c_859, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_840])).
% 7.09/2.38  tff(c_877, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_859])).
% 7.09/2.38  tff(c_2317, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2299, c_877])).
% 7.09/2.38  tff(c_2353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_64, c_58, c_2317])).
% 7.09/2.38  tff(c_2354, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_859])).
% 7.09/2.38  tff(c_3549, plain, (![C_246, D_247, B_248, A_249]: (k2_funct_1(C_246)=D_247 | k1_xboole_0=B_248 | k1_xboole_0=A_249 | ~v2_funct_1(C_246) | ~r2_relset_1(A_249, A_249, k1_partfun1(A_249, B_248, B_248, A_249, C_246, D_247), k6_partfun1(A_249)) | k2_relset_1(A_249, B_248, C_246)!=B_248 | ~m1_subset_1(D_247, k1_zfmisc_1(k2_zfmisc_1(B_248, A_249))) | ~v1_funct_2(D_247, B_248, A_249) | ~v1_funct_1(D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_2(C_246, A_249, B_248) | ~v1_funct_1(C_246))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.09/2.38  tff(c_3558, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2354, c_3549])).
% 7.09/2.38  tff(c_3566, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_700, c_189, c_765, c_3558])).
% 7.09/2.38  tff(c_3568, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3566])).
% 7.09/2.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.09/2.38  tff(c_3593, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3568, c_2])).
% 7.09/2.38  tff(c_3595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_3593])).
% 7.09/2.38  tff(c_3596, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_3566])).
% 7.09/2.38  tff(c_2707, plain, (![A_200, B_201]: (k2_funct_2(A_200, B_201)=k2_funct_1(B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~v3_funct_2(B_201, A_200, A_200) | ~v1_funct_2(B_201, A_200, A_200) | ~v1_funct_1(B_201))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.09/2.38  tff(c_2722, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2707])).
% 7.09/2.38  tff(c_2731, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2722])).
% 7.09/2.38  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_2738, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_54])).
% 7.09/2.38  tff(c_3657, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3596, c_2738])).
% 7.09/2.38  tff(c_3679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_3657])).
% 7.09/2.38  tff(c_3681, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_139])).
% 7.09/2.38  tff(c_140, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_128])).
% 7.09/2.38  tff(c_3734, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3681, c_140])).
% 7.09/2.38  tff(c_74, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | B_48=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.09/2.38  tff(c_77, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_2, c_74])).
% 7.09/2.38  tff(c_3694, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3681, c_77])).
% 7.09/2.38  tff(c_3680, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_139])).
% 7.09/2.38  tff(c_3687, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3680, c_77])).
% 7.09/2.38  tff(c_3713, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3694, c_3687])).
% 7.09/2.38  tff(c_3696, plain, (![A_49]: (A_49='#skF_3' | ~v1_xboole_0(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_3687, c_77])).
% 7.09/2.38  tff(c_3739, plain, (![A_255]: (A_255='#skF_1' | ~v1_xboole_0(A_255))), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_3696])).
% 7.09/2.38  tff(c_3746, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3734, c_3739])).
% 7.09/2.38  tff(c_3703, plain, (![A_252, B_253, D_254]: (r2_relset_1(A_252, B_253, D_254, D_254) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.09/2.38  tff(c_3712, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_3703])).
% 7.09/2.38  tff(c_3791, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3746, c_3746, c_3712])).
% 7.09/2.38  tff(c_3727, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_64])).
% 7.09/2.38  tff(c_3725, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_62])).
% 7.09/2.38  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.09/2.38  tff(c_3726, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_60])).
% 7.09/2.38  tff(c_3724, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_58])).
% 7.09/2.38  tff(c_4790, plain, (![A_317, B_318]: (k2_funct_2(A_317, B_318)=k2_funct_1(B_318) | ~m1_subset_1(B_318, k1_zfmisc_1(k2_zfmisc_1(A_317, A_317))) | ~v3_funct_2(B_318, A_317, A_317) | ~v1_funct_2(B_318, A_317, A_317) | ~v1_funct_1(B_318))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.09/2.38  tff(c_4796, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_3724, c_4790])).
% 7.09/2.38  tff(c_4805, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3727, c_3725, c_3726, c_4796])).
% 7.09/2.38  tff(c_6989, plain, (![A_361, B_362]: (m1_subset_1(k2_funct_2(A_361, B_362), k1_zfmisc_1(k2_zfmisc_1(A_361, A_361))) | ~m1_subset_1(B_362, k1_zfmisc_1(k2_zfmisc_1(A_361, A_361))) | ~v3_funct_2(B_362, A_361, A_361) | ~v1_funct_2(B_362, A_361, A_361) | ~v1_funct_1(B_362))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.09/2.38  tff(c_7030, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4805, c_6989])).
% 7.09/2.38  tff(c_7046, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3727, c_3725, c_3726, c_3724, c_7030])).
% 7.09/2.38  tff(c_12, plain, (![C_12, A_9, B_10]: (v1_xboole_0(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.09/2.38  tff(c_7075, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_7046, c_12])).
% 7.09/2.38  tff(c_7113, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3681, c_7075])).
% 7.09/2.38  tff(c_3738, plain, (![A_49]: (A_49='#skF_1' | ~v1_xboole_0(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_3696])).
% 7.09/2.38  tff(c_7144, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_7113, c_3738])).
% 7.09/2.38  tff(c_3723, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3713, c_54])).
% 7.09/2.38  tff(c_4004, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3746, c_3723])).
% 7.09/2.38  tff(c_4808, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4805, c_4004])).
% 7.09/2.38  tff(c_7179, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7144, c_4808])).
% 7.09/2.38  tff(c_7190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3791, c_7179])).
% 7.09/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.38  
% 7.09/2.38  Inference rules
% 7.09/2.38  ----------------------
% 7.09/2.38  #Ref     : 0
% 7.09/2.38  #Sup     : 1855
% 7.09/2.38  #Fact    : 0
% 7.09/2.38  #Define  : 0
% 7.09/2.38  #Split   : 17
% 7.09/2.38  #Chain   : 0
% 7.09/2.38  #Close   : 0
% 7.09/2.38  
% 7.09/2.38  Ordering : KBO
% 7.09/2.38  
% 7.09/2.38  Simplification rules
% 7.09/2.38  ----------------------
% 7.09/2.38  #Subsume      : 458
% 7.09/2.38  #Demod        : 1330
% 7.09/2.38  #Tautology    : 486
% 7.09/2.38  #SimpNegUnit  : 8
% 7.09/2.38  #BackRed      : 89
% 7.09/2.38  
% 7.09/2.38  #Partial instantiations: 0
% 7.09/2.38  #Strategies tried      : 1
% 7.09/2.38  
% 7.09/2.38  Timing (in seconds)
% 7.09/2.38  ----------------------
% 7.09/2.39  Preprocessing        : 0.39
% 7.09/2.39  Parsing              : 0.21
% 7.09/2.39  CNF conversion       : 0.03
% 7.09/2.39  Main loop            : 1.23
% 7.09/2.39  Inferencing          : 0.40
% 7.09/2.39  Reduction            : 0.42
% 7.09/2.39  Demodulation         : 0.31
% 7.09/2.39  BG Simplification    : 0.05
% 7.09/2.39  Subsumption          : 0.26
% 7.09/2.39  Abstraction          : 0.05
% 7.09/2.39  MUC search           : 0.00
% 7.09/2.39  Cooper               : 0.00
% 7.09/2.39  Total                : 1.66
% 7.09/2.39  Index Insertion      : 0.00
% 7.09/2.39  Index Deletion       : 0.00
% 7.09/2.39  Index Matching       : 0.00
% 7.09/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
