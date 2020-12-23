%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 590 expanded)
%              Number of leaves         :   50 ( 220 expanded)
%              Depth                    :   15
%              Number of atoms          :  356 (1658 expanded)
%              Number of equality atoms :   61 ( 139 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_160,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_150,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_83,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_52,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] :
      ( m1_subset_1(k1_partfun1(A_34,B_35,C_36,D_37,E_38,F_39),k1_zfmisc_1(k2_zfmisc_1(A_34,D_37)))
      | ~ m1_subset_1(F_39,k1_zfmisc_1(k2_zfmisc_1(C_36,D_37)))
      | ~ v1_funct_1(F_39)
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(E_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1756,plain,(
    ! [D_251,C_252,A_253,B_254] :
      ( D_251 = C_252
      | ~ r2_relset_1(A_253,B_254,C_252,D_251)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1766,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_1756])).

tff(c_1785,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1766])).

tff(c_1807,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1785])).

tff(c_2196,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1807])).

tff(c_2200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_2196])).

tff(c_2201,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1785])).

tff(c_2817,plain,(
    ! [D_363,A_365,C_366,E_362,B_364] :
      ( k1_xboole_0 = C_366
      | v2_funct_1(D_363)
      | ~ v2_funct_1(k1_partfun1(A_365,B_364,B_364,C_366,D_363,E_362))
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(B_364,C_366)))
      | ~ v1_funct_2(E_362,B_364,C_366)
      | ~ v1_funct_1(E_362)
      | ~ m1_subset_1(D_363,k1_zfmisc_1(k2_zfmisc_1(A_365,B_364)))
      | ~ v1_funct_2(D_363,A_365,B_364)
      | ~ v1_funct_1(D_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2821,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2201,c_2817])).

tff(c_2825,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_83,c_2821])).

tff(c_2826,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_2825])).

tff(c_30,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_194,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_206,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_194])).

tff(c_218,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_206])).

tff(c_358,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_376,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_358])).

tff(c_527,plain,(
    ! [B_106,A_107] :
      ( k2_relat_1(B_106) = A_107
      | ~ v2_funct_2(B_106,A_107)
      | ~ v5_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_542,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_376,c_527])).

tff(c_559,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_542])).

tff(c_587,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_203,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_194])).

tff(c_215,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_203])).

tff(c_36,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_84,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_1010,plain,(
    ! [C_171,A_166,E_169,F_168,D_167,B_170] :
      ( m1_subset_1(k1_partfun1(A_166,B_170,C_171,D_167,E_169,F_168),k1_zfmisc_1(k2_zfmisc_1(A_166,D_167)))
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_171,D_167)))
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_170)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_675,plain,(
    ! [D_122,C_123,A_124,B_125] :
      ( D_122 = C_123
      | ~ r2_relset_1(A_124,B_125,C_123,D_122)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_685,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_675])).

tff(c_704,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_685])).

tff(c_763,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_1016,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1010,c_763])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1016])).

tff(c_1049,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_1257,plain,(
    ! [B_205,E_200,D_203,C_202,F_204,A_201] :
      ( k1_partfun1(A_201,B_205,C_202,D_203,E_200,F_204) = k5_relat_1(E_200,F_204)
      | ~ m1_subset_1(F_204,k1_zfmisc_1(k2_zfmisc_1(C_202,D_203)))
      | ~ v1_funct_1(F_204)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1263,plain,(
    ! [A_201,B_205,E_200] :
      ( k1_partfun1(A_201,B_205,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_72,c_1257])).

tff(c_1512,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_2','#skF_1',E_236,'#skF_4') = k5_relat_1(E_236,'#skF_4')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1263])).

tff(c_1524,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1512])).

tff(c_1541,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1049,c_1524])).

tff(c_32,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1551,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_32])).

tff(c_1557,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_218,c_84,c_1551])).

tff(c_301,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(k2_relat_1(B_82),A_83)
      | ~ v5_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_319,plain,(
    ! [B_82,A_83] :
      ( k2_relat_1(B_82) = A_83
      | ~ r1_tarski(A_83,k2_relat_1(B_82))
      | ~ v5_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_301,c_4])).

tff(c_1561,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1557,c_319])).

tff(c_1566,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_376,c_1561])).

tff(c_393,plain,(
    ! [B_92,A_93] :
      ( v5_relat_1(B_92,A_93)
      | ~ r1_tarski(k2_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_412,plain,(
    ! [B_92] :
      ( v5_relat_1(B_92,k2_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_491,plain,(
    ! [B_104] :
      ( v2_funct_2(B_104,k2_relat_1(B_104))
      | ~ v5_relat_1(B_104,k2_relat_1(B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_512,plain,(
    ! [B_92] :
      ( v2_funct_2(B_92,k2_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_412,c_491])).

tff(c_1585,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_512])).

tff(c_1606,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_1585])).

tff(c_1608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_587,c_1606])).

tff(c_1609,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1620,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1609,c_26])).

tff(c_1631,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_1620])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [B_71,A_72] :
      ( ~ r1_xboole_0(B_71,A_72)
      | ~ r1_tarski(B_71,A_72)
      | v1_xboole_0(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_1735,plain,(
    ! [B_250] :
      ( v1_xboole_0(k2_relat_1(B_250))
      | ~ v5_relat_1(B_250,k1_xboole_0)
      | ~ v1_relat_1(B_250) ) ),
    inference(resolution,[status(thm)],[c_301,c_176])).

tff(c_1741,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1609,c_1735])).

tff(c_1750,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_1741])).

tff(c_1755,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1750])).

tff(c_1789,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1631,c_1755])).

tff(c_2839,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2826,c_1789])).

tff(c_2867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2839])).

tff(c_2868,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1750])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2873,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2868,c_2])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2896,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_1',B_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_2873,c_20])).

tff(c_244,plain,(
    ! [B_80,A_81] :
      ( v1_xboole_0(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_261,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_244])).

tff(c_263,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_3103,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2896,c_263])).

tff(c_3107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_3103])).

tff(c_3108,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_3113,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3108,c_2])).

tff(c_177,plain,(
    ! [A_73] :
      ( ~ r1_tarski(A_73,k1_xboole_0)
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_186,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_68] : m1_subset_1(k6_partfun1(A_68),k1_zfmisc_1(k2_zfmisc_1(A_68,A_68))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_155,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_151])).

tff(c_247,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_155,c_244])).

tff(c_259,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_247])).

tff(c_3132,plain,(
    v1_xboole_0(k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3113,c_259])).

tff(c_3151,plain,(
    ! [A_396] :
      ( A_396 = '#skF_3'
      | ~ v1_xboole_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3113,c_2])).

tff(c_3162,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3132,c_3151])).

tff(c_3183,plain,(
    v2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_83])).

tff(c_3188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_3183])).

tff(c_3189,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3234,plain,(
    ! [B_403,A_404] :
      ( v1_relat_1(B_403)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(A_404))
      | ~ v1_relat_1(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3246,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_3234])).

tff(c_3258,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3246])).

tff(c_3368,plain,(
    ! [C_412,B_413,A_414] :
      ( v5_relat_1(C_412,B_413)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_414,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3386,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_3368])).

tff(c_3243,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_3234])).

tff(c_3255,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3243])).

tff(c_3855,plain,(
    ! [E_472,D_475,C_474,B_477,F_476,A_473] :
      ( k1_partfun1(A_473,B_477,C_474,D_475,E_472,F_476) = k5_relat_1(E_472,F_476)
      | ~ m1_subset_1(F_476,k1_zfmisc_1(k2_zfmisc_1(C_474,D_475)))
      | ~ v1_funct_1(F_476)
      | ~ m1_subset_1(E_472,k1_zfmisc_1(k2_zfmisc_1(A_473,B_477)))
      | ~ v1_funct_1(E_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3861,plain,(
    ! [A_473,B_477,E_472] :
      ( k1_partfun1(A_473,B_477,'#skF_2','#skF_1',E_472,'#skF_4') = k5_relat_1(E_472,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_472,k1_zfmisc_1(k2_zfmisc_1(A_473,B_477)))
      | ~ v1_funct_1(E_472) ) ),
    inference(resolution,[status(thm)],[c_72,c_3855])).

tff(c_4073,plain,(
    ! [A_500,B_501,E_502] :
      ( k1_partfun1(A_500,B_501,'#skF_2','#skF_1',E_502,'#skF_4') = k5_relat_1(E_502,'#skF_4')
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(A_500,B_501)))
      | ~ v1_funct_1(E_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3861])).

tff(c_4082,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4073])).

tff(c_4096,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4082])).

tff(c_4105,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4096,c_52])).

tff(c_4109,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_4105])).

tff(c_3647,plain,(
    ! [D_448,C_449,A_450,B_451] :
      ( D_448 = C_449
      | ~ r2_relset_1(A_450,B_451,C_449,D_448)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3657,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_3647])).

tff(c_3676,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3657])).

tff(c_4404,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4109,c_4096,c_4096,c_3676])).

tff(c_4425,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4404,c_32])).

tff(c_4431,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3258,c_84,c_4425])).

tff(c_3443,plain,(
    ! [B_424,A_425] :
      ( r1_tarski(k2_relat_1(B_424),A_425)
      | ~ v5_relat_1(B_424,A_425)
      | ~ v1_relat_1(B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3465,plain,(
    ! [B_424,A_425] :
      ( k2_relat_1(B_424) = A_425
      | ~ r1_tarski(A_425,k2_relat_1(B_424))
      | ~ v5_relat_1(B_424,A_425)
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_3443,c_4])).

tff(c_4435,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4431,c_3465])).

tff(c_4440,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3258,c_3386,c_4435])).

tff(c_3387,plain,(
    ! [B_415,A_416] :
      ( v5_relat_1(B_415,A_416)
      | ~ r1_tarski(k2_relat_1(B_415),A_416)
      | ~ v1_relat_1(B_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3402,plain,(
    ! [B_415] :
      ( v5_relat_1(B_415,k2_relat_1(B_415))
      | ~ v1_relat_1(B_415) ) ),
    inference(resolution,[status(thm)],[c_8,c_3387])).

tff(c_3495,plain,(
    ! [B_431] :
      ( v2_funct_2(B_431,k2_relat_1(B_431))
      | ~ v5_relat_1(B_431,k2_relat_1(B_431))
      | ~ v1_relat_1(B_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3509,plain,(
    ! [B_415] :
      ( v2_funct_2(B_415,k2_relat_1(B_415))
      | ~ v1_relat_1(B_415) ) ),
    inference(resolution,[status(thm)],[c_3402,c_3495])).

tff(c_4459,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4440,c_3509])).

tff(c_4480,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3258,c_4459])).

tff(c_4482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3189,c_4480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:01:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.23  
% 6.02/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.23  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.02/2.23  
% 6.02/2.23  %Foreground sorts:
% 6.02/2.23  
% 6.02/2.23  
% 6.02/2.23  %Background operators:
% 6.02/2.23  
% 6.02/2.23  
% 6.02/2.23  %Foreground operators:
% 6.02/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.02/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.02/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.02/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.02/2.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.02/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.02/2.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.02/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.02/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.02/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.02/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.02/2.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.02/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.02/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.02/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.02/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.02/2.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.02/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.02/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.02/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.02/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.23  
% 6.02/2.25  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.02/2.25  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.02/2.25  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.02/2.25  tff(f_88, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.02/2.25  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.02/2.25  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.02/2.25  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.02/2.25  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.02/2.25  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.02/2.25  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.02/2.25  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.02/2.25  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.02/2.25  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.02/2.25  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.02/2.25  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.02/2.25  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.02/2.25  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.02/2.25  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 6.02/2.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.02/2.25  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.02/2.25  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.02/2.25  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_150, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 6.02/2.25  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.02/2.25  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_62, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.02/2.25  tff(c_38, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.02/2.25  tff(c_83, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 6.02/2.25  tff(c_52, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (m1_subset_1(k1_partfun1(A_34, B_35, C_36, D_37, E_38, F_39), k1_zfmisc_1(k2_zfmisc_1(A_34, D_37))) | ~m1_subset_1(F_39, k1_zfmisc_1(k2_zfmisc_1(C_36, D_37))) | ~v1_funct_1(F_39) | ~m1_subset_1(E_38, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(E_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.02/2.25  tff(c_58, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.02/2.25  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.02/2.25  tff(c_1756, plain, (![D_251, C_252, A_253, B_254]: (D_251=C_252 | ~r2_relset_1(A_253, B_254, C_252, D_251) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.02/2.25  tff(c_1766, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_1756])).
% 6.02/2.25  tff(c_1785, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1766])).
% 6.02/2.25  tff(c_1807, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1785])).
% 6.02/2.25  tff(c_2196, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1807])).
% 6.02/2.25  tff(c_2200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_2196])).
% 6.02/2.25  tff(c_2201, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1785])).
% 6.02/2.25  tff(c_2817, plain, (![D_363, A_365, C_366, E_362, B_364]: (k1_xboole_0=C_366 | v2_funct_1(D_363) | ~v2_funct_1(k1_partfun1(A_365, B_364, B_364, C_366, D_363, E_362)) | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(B_364, C_366))) | ~v1_funct_2(E_362, B_364, C_366) | ~v1_funct_1(E_362) | ~m1_subset_1(D_363, k1_zfmisc_1(k2_zfmisc_1(A_365, B_364))) | ~v1_funct_2(D_363, A_365, B_364) | ~v1_funct_1(D_363))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.02/2.25  tff(c_2821, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2201, c_2817])).
% 6.02/2.25  tff(c_2825, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_83, c_2821])).
% 6.02/2.25  tff(c_2826, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_150, c_2825])).
% 6.02/2.25  tff(c_30, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.02/2.25  tff(c_194, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.02/2.25  tff(c_206, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_194])).
% 6.02/2.25  tff(c_218, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_206])).
% 6.02/2.25  tff(c_358, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.02/2.25  tff(c_376, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_358])).
% 6.02/2.25  tff(c_527, plain, (![B_106, A_107]: (k2_relat_1(B_106)=A_107 | ~v2_funct_2(B_106, A_107) | ~v5_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.02/2.25  tff(c_542, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_376, c_527])).
% 6.02/2.25  tff(c_559, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_542])).
% 6.02/2.25  tff(c_587, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_559])).
% 6.02/2.25  tff(c_203, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_194])).
% 6.02/2.25  tff(c_215, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_203])).
% 6.02/2.25  tff(c_36, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.02/2.25  tff(c_84, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 6.02/2.25  tff(c_1010, plain, (![C_171, A_166, E_169, F_168, D_167, B_170]: (m1_subset_1(k1_partfun1(A_166, B_170, C_171, D_167, E_169, F_168), k1_zfmisc_1(k2_zfmisc_1(A_166, D_167))) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_171, D_167))) | ~v1_funct_1(F_168) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_170))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.02/2.25  tff(c_675, plain, (![D_122, C_123, A_124, B_125]: (D_122=C_123 | ~r2_relset_1(A_124, B_125, C_123, D_122) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.02/2.25  tff(c_685, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_675])).
% 6.02/2.25  tff(c_704, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_685])).
% 6.02/2.25  tff(c_763, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_704])).
% 6.02/2.25  tff(c_1016, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1010, c_763])).
% 6.02/2.25  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1016])).
% 6.02/2.25  tff(c_1049, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_704])).
% 6.02/2.25  tff(c_1257, plain, (![B_205, E_200, D_203, C_202, F_204, A_201]: (k1_partfun1(A_201, B_205, C_202, D_203, E_200, F_204)=k5_relat_1(E_200, F_204) | ~m1_subset_1(F_204, k1_zfmisc_1(k2_zfmisc_1(C_202, D_203))) | ~v1_funct_1(F_204) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.02/2.25  tff(c_1263, plain, (![A_201, B_205, E_200]: (k1_partfun1(A_201, B_205, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_72, c_1257])).
% 6.02/2.25  tff(c_1512, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_2', '#skF_1', E_236, '#skF_4')=k5_relat_1(E_236, '#skF_4') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1263])).
% 6.02/2.25  tff(c_1524, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1512])).
% 6.02/2.25  tff(c_1541, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1049, c_1524])).
% 6.02/2.25  tff(c_32, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.02/2.25  tff(c_1551, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1541, c_32])).
% 6.02/2.25  tff(c_1557, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_218, c_84, c_1551])).
% 6.02/2.25  tff(c_301, plain, (![B_82, A_83]: (r1_tarski(k2_relat_1(B_82), A_83) | ~v5_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.02/2.25  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.02/2.25  tff(c_319, plain, (![B_82, A_83]: (k2_relat_1(B_82)=A_83 | ~r1_tarski(A_83, k2_relat_1(B_82)) | ~v5_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_301, c_4])).
% 6.02/2.25  tff(c_1561, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1557, c_319])).
% 6.02/2.25  tff(c_1566, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_376, c_1561])).
% 6.02/2.25  tff(c_393, plain, (![B_92, A_93]: (v5_relat_1(B_92, A_93) | ~r1_tarski(k2_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.02/2.25  tff(c_412, plain, (![B_92]: (v5_relat_1(B_92, k2_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_8, c_393])).
% 6.02/2.25  tff(c_491, plain, (![B_104]: (v2_funct_2(B_104, k2_relat_1(B_104)) | ~v5_relat_1(B_104, k2_relat_1(B_104)) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.02/2.25  tff(c_512, plain, (![B_92]: (v2_funct_2(B_92, k2_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_412, c_491])).
% 6.02/2.25  tff(c_1585, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1566, c_512])).
% 6.02/2.25  tff(c_1606, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_1585])).
% 6.02/2.25  tff(c_1608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_587, c_1606])).
% 6.02/2.25  tff(c_1609, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_559])).
% 6.02/2.25  tff(c_26, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.02/2.25  tff(c_1620, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1609, c_26])).
% 6.02/2.25  tff(c_1631, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_1620])).
% 6.02/2.25  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.02/2.25  tff(c_172, plain, (![B_71, A_72]: (~r1_xboole_0(B_71, A_72) | ~r1_tarski(B_71, A_72) | v1_xboole_0(B_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.02/2.25  tff(c_176, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_172])).
% 6.02/2.25  tff(c_1735, plain, (![B_250]: (v1_xboole_0(k2_relat_1(B_250)) | ~v5_relat_1(B_250, k1_xboole_0) | ~v1_relat_1(B_250))), inference(resolution, [status(thm)], [c_301, c_176])).
% 6.02/2.25  tff(c_1741, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1609, c_1735])).
% 6.02/2.25  tff(c_1750, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_1741])).
% 6.02/2.25  tff(c_1755, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1750])).
% 6.02/2.25  tff(c_1789, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_1631, c_1755])).
% 6.02/2.25  tff(c_2839, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2826, c_1789])).
% 6.02/2.25  tff(c_2867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2839])).
% 6.02/2.25  tff(c_2868, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_1750])).
% 6.02/2.25  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.02/2.25  tff(c_2873, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2868, c_2])).
% 6.02/2.25  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.25  tff(c_2896, plain, (![B_9]: (k2_zfmisc_1('#skF_1', B_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_2873, c_20])).
% 6.02/2.25  tff(c_244, plain, (![B_80, A_81]: (v1_xboole_0(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.02/2.25  tff(c_261, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_244])).
% 6.02/2.25  tff(c_263, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_261])).
% 6.02/2.25  tff(c_3103, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2896, c_263])).
% 6.02/2.25  tff(c_3107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2868, c_3103])).
% 6.02/2.25  tff(c_3108, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_261])).
% 6.02/2.25  tff(c_3113, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3108, c_2])).
% 6.02/2.25  tff(c_177, plain, (![A_73]: (~r1_tarski(A_73, k1_xboole_0) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_12, c_172])).
% 6.02/2.25  tff(c_186, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_177])).
% 6.02/2.25  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.25  tff(c_151, plain, (![A_68]: (m1_subset_1(k6_partfun1(A_68), k1_zfmisc_1(k2_zfmisc_1(A_68, A_68))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.02/2.25  tff(c_155, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_151])).
% 6.02/2.25  tff(c_247, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_155, c_244])).
% 6.02/2.25  tff(c_259, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_247])).
% 6.02/2.25  tff(c_3132, plain, (v1_xboole_0(k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3113, c_259])).
% 6.02/2.25  tff(c_3151, plain, (![A_396]: (A_396='#skF_3' | ~v1_xboole_0(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_3113, c_2])).
% 6.02/2.25  tff(c_3162, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3132, c_3151])).
% 6.02/2.25  tff(c_3183, plain, (v2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3162, c_83])).
% 6.02/2.25  tff(c_3188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_3183])).
% 6.02/2.25  tff(c_3189, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 6.02/2.25  tff(c_3234, plain, (![B_403, A_404]: (v1_relat_1(B_403) | ~m1_subset_1(B_403, k1_zfmisc_1(A_404)) | ~v1_relat_1(A_404))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.02/2.25  tff(c_3246, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_3234])).
% 6.02/2.25  tff(c_3258, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3246])).
% 6.02/2.25  tff(c_3368, plain, (![C_412, B_413, A_414]: (v5_relat_1(C_412, B_413) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_414, B_413))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.02/2.25  tff(c_3386, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_3368])).
% 6.02/2.25  tff(c_3243, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_3234])).
% 6.02/2.25  tff(c_3255, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3243])).
% 6.02/2.25  tff(c_3855, plain, (![E_472, D_475, C_474, B_477, F_476, A_473]: (k1_partfun1(A_473, B_477, C_474, D_475, E_472, F_476)=k5_relat_1(E_472, F_476) | ~m1_subset_1(F_476, k1_zfmisc_1(k2_zfmisc_1(C_474, D_475))) | ~v1_funct_1(F_476) | ~m1_subset_1(E_472, k1_zfmisc_1(k2_zfmisc_1(A_473, B_477))) | ~v1_funct_1(E_472))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.02/2.25  tff(c_3861, plain, (![A_473, B_477, E_472]: (k1_partfun1(A_473, B_477, '#skF_2', '#skF_1', E_472, '#skF_4')=k5_relat_1(E_472, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_472, k1_zfmisc_1(k2_zfmisc_1(A_473, B_477))) | ~v1_funct_1(E_472))), inference(resolution, [status(thm)], [c_72, c_3855])).
% 6.02/2.25  tff(c_4073, plain, (![A_500, B_501, E_502]: (k1_partfun1(A_500, B_501, '#skF_2', '#skF_1', E_502, '#skF_4')=k5_relat_1(E_502, '#skF_4') | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(A_500, B_501))) | ~v1_funct_1(E_502))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3861])).
% 6.02/2.25  tff(c_4082, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4073])).
% 6.02/2.25  tff(c_4096, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4082])).
% 6.02/2.25  tff(c_4105, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4096, c_52])).
% 6.02/2.25  tff(c_4109, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_4105])).
% 6.02/2.25  tff(c_3647, plain, (![D_448, C_449, A_450, B_451]: (D_448=C_449 | ~r2_relset_1(A_450, B_451, C_449, D_448) | ~m1_subset_1(D_448, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.02/2.25  tff(c_3657, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_3647])).
% 6.02/2.25  tff(c_3676, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3657])).
% 6.02/2.25  tff(c_4404, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4109, c_4096, c_4096, c_3676])).
% 6.02/2.25  tff(c_4425, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4404, c_32])).
% 6.02/2.25  tff(c_4431, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3258, c_84, c_4425])).
% 6.02/2.25  tff(c_3443, plain, (![B_424, A_425]: (r1_tarski(k2_relat_1(B_424), A_425) | ~v5_relat_1(B_424, A_425) | ~v1_relat_1(B_424))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.02/2.25  tff(c_3465, plain, (![B_424, A_425]: (k2_relat_1(B_424)=A_425 | ~r1_tarski(A_425, k2_relat_1(B_424)) | ~v5_relat_1(B_424, A_425) | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_3443, c_4])).
% 6.02/2.25  tff(c_4435, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4431, c_3465])).
% 6.02/2.25  tff(c_4440, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3258, c_3386, c_4435])).
% 6.02/2.25  tff(c_3387, plain, (![B_415, A_416]: (v5_relat_1(B_415, A_416) | ~r1_tarski(k2_relat_1(B_415), A_416) | ~v1_relat_1(B_415))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.02/2.25  tff(c_3402, plain, (![B_415]: (v5_relat_1(B_415, k2_relat_1(B_415)) | ~v1_relat_1(B_415))), inference(resolution, [status(thm)], [c_8, c_3387])).
% 6.02/2.25  tff(c_3495, plain, (![B_431]: (v2_funct_2(B_431, k2_relat_1(B_431)) | ~v5_relat_1(B_431, k2_relat_1(B_431)) | ~v1_relat_1(B_431))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.02/2.25  tff(c_3509, plain, (![B_415]: (v2_funct_2(B_415, k2_relat_1(B_415)) | ~v1_relat_1(B_415))), inference(resolution, [status(thm)], [c_3402, c_3495])).
% 6.02/2.25  tff(c_4459, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4440, c_3509])).
% 6.02/2.25  tff(c_4480, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3258, c_4459])).
% 6.02/2.25  tff(c_4482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3189, c_4480])).
% 6.02/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.25  
% 6.02/2.25  Inference rules
% 6.02/2.25  ----------------------
% 6.02/2.25  #Ref     : 0
% 6.02/2.25  #Sup     : 914
% 6.02/2.25  #Fact    : 0
% 6.02/2.25  #Define  : 0
% 6.02/2.25  #Split   : 16
% 6.02/2.25  #Chain   : 0
% 6.02/2.25  #Close   : 0
% 6.02/2.25  
% 6.02/2.25  Ordering : KBO
% 6.02/2.25  
% 6.02/2.25  Simplification rules
% 6.02/2.25  ----------------------
% 6.02/2.25  #Subsume      : 107
% 6.02/2.25  #Demod        : 889
% 6.02/2.25  #Tautology    : 305
% 6.02/2.25  #SimpNegUnit  : 4
% 6.02/2.25  #BackRed      : 104
% 6.02/2.25  
% 6.02/2.25  #Partial instantiations: 0
% 6.02/2.25  #Strategies tried      : 1
% 6.02/2.25  
% 6.02/2.25  Timing (in seconds)
% 6.02/2.25  ----------------------
% 6.43/2.26  Preprocessing        : 0.36
% 6.43/2.26  Parsing              : 0.19
% 6.43/2.26  CNF conversion       : 0.03
% 6.43/2.26  Main loop            : 1.04
% 6.43/2.26  Inferencing          : 0.35
% 6.43/2.26  Reduction            : 0.39
% 6.43/2.26  Demodulation         : 0.28
% 6.43/2.26  BG Simplification    : 0.04
% 6.43/2.26  Subsumption          : 0.17
% 6.43/2.26  Abstraction          : 0.04
% 6.43/2.26  MUC search           : 0.00
% 6.43/2.26  Cooper               : 0.00
% 6.43/2.26  Total                : 1.45
% 6.43/2.26  Index Insertion      : 0.00
% 6.43/2.26  Index Deletion       : 0.00
% 6.43/2.26  Index Matching       : 0.00
% 6.43/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
