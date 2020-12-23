%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:09 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 544 expanded)
%              Number of leaves         :   44 ( 206 expanded)
%              Depth                    :   12
%              Number of atoms          :  370 (1607 expanded)
%              Number of equality atoms :   82 ( 251 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_168,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_87,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_126,axiom,(
    ! [A,B,C] :
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_148,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_124,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_153,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_171,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_153])).

tff(c_344,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_361,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_344])).

tff(c_405,plain,(
    ! [B_88,A_89] :
      ( k2_relat_1(B_88) = A_89
      | ~ v2_funct_2(B_88,A_89)
      | ~ v5_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_411,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_361,c_405])).

tff(c_426,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_411])).

tff(c_442,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_379,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_relset_1(A_84,B_85,D_86,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_389,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_79,c_379])).

tff(c_471,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_488,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_471])).

tff(c_697,plain,(
    ! [B_126,A_127,E_125,D_124,C_123,F_122] :
      ( m1_subset_1(k1_partfun1(A_127,B_126,C_123,D_124,E_125,F_122),k1_zfmisc_1(k2_zfmisc_1(A_127,D_124)))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_123,D_124)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_1(E_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_489,plain,(
    ! [D_97,C_98,A_99,B_100] :
      ( D_97 = C_98
      | ~ r2_relset_1(A_99,B_100,C_98,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_499,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_489])).

tff(c_518,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_499])).

tff(c_531,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_518])).

tff(c_708,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_697,c_531])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_708])).

tff(c_730,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_1344,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( k2_relset_1(A_204,B_205,C_206) = B_205
      | ~ r2_relset_1(B_205,B_205,k1_partfun1(B_205,A_204,A_204,B_205,D_207,C_206),k6_partfun1(B_205))
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(B_205,A_204)))
      | ~ v1_funct_2(D_207,B_205,A_204)
      | ~ v1_funct_1(D_207)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_2(C_206,A_204,B_205)
      | ~ v1_funct_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1347,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_1344])).

tff(c_1349,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_389,c_488,c_1347])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [B_66,A_67] :
      ( v5_relat_1(B_66,A_67)
      | ~ r1_tarski(k2_relat_1(B_66),A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_244,plain,(
    ! [B_66] :
      ( v5_relat_1(B_66,k2_relat_1(B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_362,plain,(
    ! [B_83] :
      ( v2_funct_2(B_83,k2_relat_1(B_83))
      | ~ v5_relat_1(B_83,k2_relat_1(B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_373,plain,(
    ! [B_66] :
      ( v2_funct_2(B_66,k2_relat_1(B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_244,c_362])).

tff(c_1362,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_373])).

tff(c_1381,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_1362])).

tff(c_1383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_1381])).

tff(c_1384,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_24,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_186,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_171,c_24])).

tff(c_189,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_1386,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_189])).

tff(c_32,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_1799,plain,(
    ! [B_248,C_245,E_247,F_244,A_249,D_246] :
      ( m1_subset_1(k1_partfun1(A_249,B_248,C_245,D_246,E_247,F_244),k1_zfmisc_1(k2_zfmisc_1(A_249,D_246)))
      | ~ m1_subset_1(F_244,k1_zfmisc_1(k2_zfmisc_1(C_245,D_246)))
      | ~ v1_funct_1(F_244)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_1(E_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1587,plain,(
    ! [D_221,C_222,A_223,B_224] :
      ( D_221 = C_222
      | ~ r2_relset_1(A_223,B_224,C_222,D_221)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1597,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_1587])).

tff(c_1616,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1597])).

tff(c_1698,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1616])).

tff(c_1810,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1799,c_1698])).

tff(c_1831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1810])).

tff(c_1832,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1616])).

tff(c_2077,plain,(
    ! [C_290,B_289,A_287,D_291,E_288] :
      ( k1_xboole_0 = C_290
      | v2_funct_1(D_291)
      | ~ v2_funct_1(k1_partfun1(A_287,B_289,B_289,C_290,D_291,E_288))
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(B_289,C_290)))
      | ~ v1_funct_2(E_288,B_289,C_290)
      | ~ v1_funct_1(E_288)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(A_287,B_289)))
      | ~ v1_funct_2(D_291,A_287,B_289)
      | ~ v1_funct_1(D_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2079,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_2077])).

tff(c_2081,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_80,c_2079])).

tff(c_2083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1386,c_2081])).

tff(c_2084,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_2085,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_2105,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_2085])).

tff(c_170,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_153])).

tff(c_26,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_179,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_170,c_26])).

tff(c_2148,plain,
    ( k1_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_2084,c_179])).

tff(c_2149,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2148])).

tff(c_52,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2479,plain,(
    ! [D_334,C_335,A_336,B_337] :
      ( D_334 = C_335
      | ~ r2_relset_1(A_336,B_337,C_335,D_334)
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2487,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_2479])).

tff(c_2502,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2487])).

tff(c_2748,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2502])).

tff(c_2751,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2748])).

tff(c_2755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_2751])).

tff(c_2756,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2502])).

tff(c_62,plain,(
    ! [E_44,D_42,A_39,C_41,B_40] :
      ( k1_xboole_0 = C_41
      | v2_funct_1(D_42)
      | ~ v2_funct_1(k1_partfun1(A_39,B_40,B_40,C_41,D_42,E_44))
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(B_40,C_41)))
      | ~ v1_funct_2(E_44,B_40,C_41)
      | ~ v1_funct_1(E_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2875,plain,(
    ! [D_391,B_389,C_390,E_388,A_387] :
      ( C_390 = '#skF_4'
      | v2_funct_1(D_391)
      | ~ v2_funct_1(k1_partfun1(A_387,B_389,B_389,C_390,D_391,E_388))
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1(B_389,C_390)))
      | ~ v1_funct_2(E_388,B_389,C_390)
      | ~ v1_funct_1(E_388)
      | ~ m1_subset_1(D_391,k1_zfmisc_1(k2_zfmisc_1(A_387,B_389)))
      | ~ v1_funct_2(D_391,A_387,B_389)
      | ~ v1_funct_1(D_391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_62])).

tff(c_2877,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_2875])).

tff(c_2879,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_80,c_2877])).

tff(c_2880,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_2879])).

tff(c_2336,plain,(
    ! [C_318,A_319,B_320] :
      ( v4_relat_1(C_318,A_319)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2352,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_2336])).

tff(c_2899,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_2352])).

tff(c_2293,plain,(
    ! [B_312,A_313] :
      ( r1_tarski(k1_relat_1(B_312),A_313)
      | ~ v4_relat_1(B_312,A_313)
      | ~ v1_relat_1(B_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [B_8] : v5_relat_1(k1_xboole_0,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2096,plain,(
    ! [B_8] : v5_relat_1('#skF_4',B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_18])).

tff(c_2243,plain,(
    ! [B_307,A_308] :
      ( r1_tarski(k2_relat_1(B_307),A_308)
      | ~ v5_relat_1(B_307,A_308)
      | ~ v1_relat_1(B_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2251,plain,(
    ! [A_308] :
      ( r1_tarski('#skF_4',A_308)
      | ~ v5_relat_1('#skF_4',A_308)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2105,c_2243])).

tff(c_2256,plain,(
    ! [A_309] : r1_tarski('#skF_4',A_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_2096,c_2251])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2259,plain,(
    ! [A_309] :
      ( A_309 = '#skF_4'
      | ~ r1_tarski(A_309,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2256,c_2])).

tff(c_2303,plain,(
    ! [B_312] :
      ( k1_relat_1(B_312) = '#skF_4'
      | ~ v4_relat_1(B_312,'#skF_4')
      | ~ v1_relat_1(B_312) ) ),
    inference(resolution,[status(thm)],[c_2293,c_2259])).

tff(c_2912,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2899,c_2303])).

tff(c_2915,plain,(
    k1_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_2912])).

tff(c_2917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2149,c_2915])).

tff(c_2918,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2148])).

tff(c_178,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_170,c_24])).

tff(c_188,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_2086,plain,(
    k2_relat_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_188])).

tff(c_2920,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2918,c_2086])).

tff(c_2929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2105,c_2920])).

tff(c_2930,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_100,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_28])).

tff(c_119,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_80])).

tff(c_2935,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2930,c_119])).

tff(c_2944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_2935])).

tff(c_2945,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2994,plain,(
    ! [C_399,A_400,B_401] :
      ( v1_relat_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3012,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2994])).

tff(c_3270,plain,(
    ! [A_430,B_431,D_432] :
      ( r2_relset_1(A_430,B_431,D_432,D_432)
      | ~ m1_subset_1(D_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3280,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_79,c_3270])).

tff(c_3283,plain,(
    ! [A_433,B_434,C_435] :
      ( k2_relset_1(A_433,B_434,C_435) = k2_relat_1(C_435)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_433,B_434))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3300,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3283])).

tff(c_3313,plain,(
    ! [D_436,C_437,A_438,B_439] :
      ( D_436 = C_437
      | ~ r2_relset_1(A_438,B_439,C_437,D_436)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3321,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_3313])).

tff(c_3336,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_3321])).

tff(c_3575,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3336])).

tff(c_3578,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3575])).

tff(c_3582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_3578])).

tff(c_3583,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3336])).

tff(c_3830,plain,(
    ! [A_512,B_513,C_514,D_515] :
      ( k2_relset_1(A_512,B_513,C_514) = B_513
      | ~ r2_relset_1(B_513,B_513,k1_partfun1(B_513,A_512,A_512,B_513,D_515,C_514),k6_partfun1(B_513))
      | ~ m1_subset_1(D_515,k1_zfmisc_1(k2_zfmisc_1(B_513,A_512)))
      | ~ v1_funct_2(D_515,B_513,A_512)
      | ~ v1_funct_1(D_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513)))
      | ~ v1_funct_2(C_514,A_512,B_513)
      | ~ v1_funct_1(C_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3833,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3583,c_3830])).

tff(c_3838,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_3280,c_3300,c_3833])).

tff(c_3064,plain,(
    ! [B_408,A_409] :
      ( v5_relat_1(B_408,A_409)
      | ~ r1_tarski(k2_relat_1(B_408),A_409)
      | ~ v1_relat_1(B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3078,plain,(
    ! [B_408] :
      ( v5_relat_1(B_408,k2_relat_1(B_408))
      | ~ v1_relat_1(B_408) ) ),
    inference(resolution,[status(thm)],[c_6,c_3064])).

tff(c_3196,plain,(
    ! [B_424] :
      ( v2_funct_2(B_424,k2_relat_1(B_424))
      | ~ v5_relat_1(B_424,k2_relat_1(B_424))
      | ~ v1_relat_1(B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3207,plain,(
    ! [B_408] :
      ( v2_funct_2(B_408,k2_relat_1(B_408))
      | ~ v1_relat_1(B_408) ) ),
    inference(resolution,[status(thm)],[c_3078,c_3196])).

tff(c_3852,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3838,c_3207])).

tff(c_3871,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_3852])).

tff(c_3873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2945,c_3871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:58:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.10  
% 5.71/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.11  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.71/2.11  
% 5.71/2.11  %Foreground sorts:
% 5.71/2.11  
% 5.71/2.11  
% 5.71/2.11  %Background operators:
% 5.71/2.11  
% 5.71/2.11  
% 5.71/2.11  %Foreground operators:
% 5.71/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.71/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.71/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.71/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.71/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.71/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.71/2.11  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.71/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.71/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.71/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.71/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.71/2.11  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.71/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.71/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.71/2.11  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.71/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.71/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.71/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.71/2.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.71/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.71/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.71/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.71/2.11  
% 5.92/2.13  tff(f_168, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.92/2.13  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.92/2.13  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.92/2.13  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.92/2.13  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.92/2.13  tff(f_87, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.92/2.13  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.92/2.13  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.92/2.13  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.92/2.13  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.92/2.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.92/2.13  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.92/2.13  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.92/2.13  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.92/2.13  tff(f_148, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.92/2.13  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.92/2.13  tff(f_47, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 5.92/2.13  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.92/2.13  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_124, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 5.92/2.13  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_153, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.92/2.13  tff(c_171, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_153])).
% 5.92/2.13  tff(c_344, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.92/2.13  tff(c_361, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_344])).
% 5.92/2.13  tff(c_405, plain, (![B_88, A_89]: (k2_relat_1(B_88)=A_89 | ~v2_funct_2(B_88, A_89) | ~v5_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.92/2.13  tff(c_411, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_361, c_405])).
% 5.92/2.13  tff(c_426, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_411])).
% 5.92/2.13  tff(c_442, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_426])).
% 5.92/2.13  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_56, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.92/2.13  tff(c_46, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.92/2.13  tff(c_79, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46])).
% 5.92/2.13  tff(c_379, plain, (![A_84, B_85, D_86]: (r2_relset_1(A_84, B_85, D_86, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.92/2.13  tff(c_389, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_79, c_379])).
% 5.92/2.13  tff(c_471, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.92/2.13  tff(c_488, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_471])).
% 5.92/2.13  tff(c_697, plain, (![B_126, A_127, E_125, D_124, C_123, F_122]: (m1_subset_1(k1_partfun1(A_127, B_126, C_123, D_124, E_125, F_122), k1_zfmisc_1(k2_zfmisc_1(A_127, D_124))) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_123, D_124))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_1(E_125))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.92/2.13  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.92/2.13  tff(c_489, plain, (![D_97, C_98, A_99, B_100]: (D_97=C_98 | ~r2_relset_1(A_99, B_100, C_98, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.92/2.13  tff(c_499, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_489])).
% 5.92/2.13  tff(c_518, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_499])).
% 5.92/2.13  tff(c_531, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_518])).
% 5.92/2.13  tff(c_708, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_697, c_531])).
% 5.92/2.13  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_708])).
% 5.92/2.13  tff(c_730, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_518])).
% 5.92/2.13  tff(c_1344, plain, (![A_204, B_205, C_206, D_207]: (k2_relset_1(A_204, B_205, C_206)=B_205 | ~r2_relset_1(B_205, B_205, k1_partfun1(B_205, A_204, A_204, B_205, D_207, C_206), k6_partfun1(B_205)) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(B_205, A_204))) | ~v1_funct_2(D_207, B_205, A_204) | ~v1_funct_1(D_207) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_2(C_206, A_204, B_205) | ~v1_funct_1(C_206))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.92/2.13  tff(c_1347, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_730, c_1344])).
% 5.92/2.13  tff(c_1349, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_389, c_488, c_1347])).
% 5.92/2.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.13  tff(c_234, plain, (![B_66, A_67]: (v5_relat_1(B_66, A_67) | ~r1_tarski(k2_relat_1(B_66), A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.92/2.13  tff(c_244, plain, (![B_66]: (v5_relat_1(B_66, k2_relat_1(B_66)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_6, c_234])).
% 5.92/2.13  tff(c_362, plain, (![B_83]: (v2_funct_2(B_83, k2_relat_1(B_83)) | ~v5_relat_1(B_83, k2_relat_1(B_83)) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.92/2.13  tff(c_373, plain, (![B_66]: (v2_funct_2(B_66, k2_relat_1(B_66)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_244, c_362])).
% 5.92/2.13  tff(c_1362, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_373])).
% 5.92/2.13  tff(c_1381, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_1362])).
% 5.92/2.13  tff(c_1383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_1381])).
% 5.92/2.13  tff(c_1384, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_426])).
% 5.92/2.13  tff(c_24, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.92/2.13  tff(c_186, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_171, c_24])).
% 5.92/2.13  tff(c_189, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_186])).
% 5.92/2.13  tff(c_1386, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_189])).
% 5.92/2.13  tff(c_32, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.92/2.13  tff(c_80, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 5.92/2.13  tff(c_1799, plain, (![B_248, C_245, E_247, F_244, A_249, D_246]: (m1_subset_1(k1_partfun1(A_249, B_248, C_245, D_246, E_247, F_244), k1_zfmisc_1(k2_zfmisc_1(A_249, D_246))) | ~m1_subset_1(F_244, k1_zfmisc_1(k2_zfmisc_1(C_245, D_246))) | ~v1_funct_1(F_244) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_1(E_247))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.92/2.13  tff(c_1587, plain, (![D_221, C_222, A_223, B_224]: (D_221=C_222 | ~r2_relset_1(A_223, B_224, C_222, D_221) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.92/2.13  tff(c_1597, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_1587])).
% 5.92/2.13  tff(c_1616, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1597])).
% 5.92/2.13  tff(c_1698, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1616])).
% 5.92/2.13  tff(c_1810, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1799, c_1698])).
% 5.92/2.13  tff(c_1831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1810])).
% 5.92/2.13  tff(c_1832, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1616])).
% 5.92/2.13  tff(c_2077, plain, (![C_290, B_289, A_287, D_291, E_288]: (k1_xboole_0=C_290 | v2_funct_1(D_291) | ~v2_funct_1(k1_partfun1(A_287, B_289, B_289, C_290, D_291, E_288)) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(B_289, C_290))) | ~v1_funct_2(E_288, B_289, C_290) | ~v1_funct_1(E_288) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(A_287, B_289))) | ~v1_funct_2(D_291, A_287, B_289) | ~v1_funct_1(D_291))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.92/2.13  tff(c_2079, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1832, c_2077])).
% 5.92/2.13  tff(c_2081, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_80, c_2079])).
% 5.92/2.13  tff(c_2083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_1386, c_2081])).
% 5.92/2.13  tff(c_2084, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_186])).
% 5.92/2.13  tff(c_2085, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 5.92/2.13  tff(c_2105, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_2085])).
% 5.92/2.13  tff(c_170, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_153])).
% 5.92/2.13  tff(c_26, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.92/2.13  tff(c_179, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_170, c_26])).
% 5.92/2.13  tff(c_2148, plain, (k1_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_2084, c_179])).
% 5.92/2.13  tff(c_2149, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2148])).
% 5.92/2.13  tff(c_52, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.92/2.13  tff(c_2479, plain, (![D_334, C_335, A_336, B_337]: (D_334=C_335 | ~r2_relset_1(A_336, B_337, C_335, D_334) | ~m1_subset_1(D_334, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.92/2.13  tff(c_2487, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_2479])).
% 5.92/2.13  tff(c_2502, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_2487])).
% 5.92/2.13  tff(c_2748, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2502])).
% 5.92/2.13  tff(c_2751, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2748])).
% 5.92/2.13  tff(c_2755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_2751])).
% 5.92/2.13  tff(c_2756, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2502])).
% 5.92/2.13  tff(c_62, plain, (![E_44, D_42, A_39, C_41, B_40]: (k1_xboole_0=C_41 | v2_funct_1(D_42) | ~v2_funct_1(k1_partfun1(A_39, B_40, B_40, C_41, D_42, E_44)) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(B_40, C_41))) | ~v1_funct_2(E_44, B_40, C_41) | ~v1_funct_1(E_44) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.92/2.13  tff(c_2875, plain, (![D_391, B_389, C_390, E_388, A_387]: (C_390='#skF_4' | v2_funct_1(D_391) | ~v2_funct_1(k1_partfun1(A_387, B_389, B_389, C_390, D_391, E_388)) | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1(B_389, C_390))) | ~v1_funct_2(E_388, B_389, C_390) | ~v1_funct_1(E_388) | ~m1_subset_1(D_391, k1_zfmisc_1(k2_zfmisc_1(A_387, B_389))) | ~v1_funct_2(D_391, A_387, B_389) | ~v1_funct_1(D_391))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_62])).
% 5.92/2.13  tff(c_2877, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2756, c_2875])).
% 5.92/2.13  tff(c_2879, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_80, c_2877])).
% 5.92/2.13  tff(c_2880, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_124, c_2879])).
% 5.92/2.13  tff(c_2336, plain, (![C_318, A_319, B_320]: (v4_relat_1(C_318, A_319) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.92/2.13  tff(c_2352, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_2336])).
% 5.92/2.13  tff(c_2899, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_2352])).
% 5.92/2.13  tff(c_2293, plain, (![B_312, A_313]: (r1_tarski(k1_relat_1(B_312), A_313) | ~v4_relat_1(B_312, A_313) | ~v1_relat_1(B_312))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.13  tff(c_18, plain, (![B_8]: (v5_relat_1(k1_xboole_0, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.92/2.13  tff(c_2096, plain, (![B_8]: (v5_relat_1('#skF_4', B_8))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_18])).
% 5.92/2.13  tff(c_2243, plain, (![B_307, A_308]: (r1_tarski(k2_relat_1(B_307), A_308) | ~v5_relat_1(B_307, A_308) | ~v1_relat_1(B_307))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.92/2.13  tff(c_2251, plain, (![A_308]: (r1_tarski('#skF_4', A_308) | ~v5_relat_1('#skF_4', A_308) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2105, c_2243])).
% 5.92/2.13  tff(c_2256, plain, (![A_309]: (r1_tarski('#skF_4', A_309))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_2096, c_2251])).
% 5.92/2.13  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.13  tff(c_2259, plain, (![A_309]: (A_309='#skF_4' | ~r1_tarski(A_309, '#skF_4'))), inference(resolution, [status(thm)], [c_2256, c_2])).
% 5.92/2.13  tff(c_2303, plain, (![B_312]: (k1_relat_1(B_312)='#skF_4' | ~v4_relat_1(B_312, '#skF_4') | ~v1_relat_1(B_312))), inference(resolution, [status(thm)], [c_2293, c_2259])).
% 5.92/2.13  tff(c_2912, plain, (k1_relat_1('#skF_3')='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2899, c_2303])).
% 5.92/2.13  tff(c_2915, plain, (k1_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_2912])).
% 5.92/2.13  tff(c_2917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2149, c_2915])).
% 5.92/2.13  tff(c_2918, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2148])).
% 5.92/2.13  tff(c_178, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_170, c_24])).
% 5.92/2.13  tff(c_188, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_178])).
% 5.92/2.13  tff(c_2086, plain, (k2_relat_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_188])).
% 5.92/2.13  tff(c_2920, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2918, c_2086])).
% 5.92/2.13  tff(c_2929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2105, c_2920])).
% 5.92/2.13  tff(c_2930, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_178])).
% 5.92/2.13  tff(c_100, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.92/2.13  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.92/2.13  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_28])).
% 5.92/2.13  tff(c_119, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_80])).
% 5.92/2.13  tff(c_2935, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2930, c_119])).
% 5.92/2.13  tff(c_2944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_2935])).
% 5.92/2.13  tff(c_2945, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 5.92/2.13  tff(c_2994, plain, (![C_399, A_400, B_401]: (v1_relat_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.92/2.13  tff(c_3012, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2994])).
% 5.92/2.13  tff(c_3270, plain, (![A_430, B_431, D_432]: (r2_relset_1(A_430, B_431, D_432, D_432) | ~m1_subset_1(D_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.92/2.13  tff(c_3280, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_79, c_3270])).
% 5.92/2.13  tff(c_3283, plain, (![A_433, B_434, C_435]: (k2_relset_1(A_433, B_434, C_435)=k2_relat_1(C_435) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(A_433, B_434))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.92/2.13  tff(c_3300, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_3283])).
% 5.92/2.13  tff(c_3313, plain, (![D_436, C_437, A_438, B_439]: (D_436=C_437 | ~r2_relset_1(A_438, B_439, C_437, D_436) | ~m1_subset_1(D_436, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.92/2.13  tff(c_3321, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_3313])).
% 5.92/2.13  tff(c_3336, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_3321])).
% 5.92/2.13  tff(c_3575, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3336])).
% 5.92/2.13  tff(c_3578, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3575])).
% 5.92/2.13  tff(c_3582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_3578])).
% 5.92/2.13  tff(c_3583, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3336])).
% 5.92/2.13  tff(c_3830, plain, (![A_512, B_513, C_514, D_515]: (k2_relset_1(A_512, B_513, C_514)=B_513 | ~r2_relset_1(B_513, B_513, k1_partfun1(B_513, A_512, A_512, B_513, D_515, C_514), k6_partfun1(B_513)) | ~m1_subset_1(D_515, k1_zfmisc_1(k2_zfmisc_1(B_513, A_512))) | ~v1_funct_2(D_515, B_513, A_512) | ~v1_funct_1(D_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))) | ~v1_funct_2(C_514, A_512, B_513) | ~v1_funct_1(C_514))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.92/2.13  tff(c_3833, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3583, c_3830])).
% 5.92/2.13  tff(c_3838, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_3280, c_3300, c_3833])).
% 5.92/2.13  tff(c_3064, plain, (![B_408, A_409]: (v5_relat_1(B_408, A_409) | ~r1_tarski(k2_relat_1(B_408), A_409) | ~v1_relat_1(B_408))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.92/2.13  tff(c_3078, plain, (![B_408]: (v5_relat_1(B_408, k2_relat_1(B_408)) | ~v1_relat_1(B_408))), inference(resolution, [status(thm)], [c_6, c_3064])).
% 5.92/2.13  tff(c_3196, plain, (![B_424]: (v2_funct_2(B_424, k2_relat_1(B_424)) | ~v5_relat_1(B_424, k2_relat_1(B_424)) | ~v1_relat_1(B_424))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.92/2.13  tff(c_3207, plain, (![B_408]: (v2_funct_2(B_408, k2_relat_1(B_408)) | ~v1_relat_1(B_408))), inference(resolution, [status(thm)], [c_3078, c_3196])).
% 5.92/2.13  tff(c_3852, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3838, c_3207])).
% 5.92/2.13  tff(c_3871, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_3852])).
% 5.92/2.13  tff(c_3873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2945, c_3871])).
% 5.92/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.13  
% 5.92/2.13  Inference rules
% 5.92/2.13  ----------------------
% 5.92/2.13  #Ref     : 0
% 5.92/2.13  #Sup     : 753
% 5.92/2.13  #Fact    : 0
% 5.92/2.13  #Define  : 0
% 5.92/2.13  #Split   : 28
% 5.92/2.13  #Chain   : 0
% 5.92/2.13  #Close   : 0
% 5.92/2.13  
% 5.92/2.13  Ordering : KBO
% 5.92/2.13  
% 5.92/2.13  Simplification rules
% 5.92/2.13  ----------------------
% 5.92/2.13  #Subsume      : 106
% 5.92/2.13  #Demod        : 973
% 5.92/2.13  #Tautology    : 286
% 5.92/2.13  #SimpNegUnit  : 9
% 5.92/2.13  #BackRed      : 91
% 5.92/2.13  
% 5.92/2.13  #Partial instantiations: 0
% 5.92/2.13  #Strategies tried      : 1
% 5.92/2.13  
% 5.92/2.13  Timing (in seconds)
% 5.92/2.13  ----------------------
% 5.92/2.14  Preprocessing        : 0.35
% 5.92/2.14  Parsing              : 0.19
% 5.92/2.14  CNF conversion       : 0.03
% 5.92/2.14  Main loop            : 0.99
% 5.92/2.14  Inferencing          : 0.36
% 5.92/2.14  Reduction            : 0.35
% 5.92/2.14  Demodulation         : 0.25
% 5.92/2.14  BG Simplification    : 0.03
% 5.92/2.14  Subsumption          : 0.16
% 5.92/2.14  Abstraction          : 0.04
% 5.92/2.14  MUC search           : 0.00
% 5.92/2.14  Cooper               : 0.00
% 5.92/2.14  Total                : 1.40
% 5.92/2.14  Index Insertion      : 0.00
% 5.92/2.14  Index Deletion       : 0.00
% 5.92/2.14  Index Matching       : 0.00
% 5.92/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
