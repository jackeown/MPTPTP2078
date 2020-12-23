%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:16 EST 2020

% Result     : Timeout 57.28s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  259 (20120 expanded)
%              Number of leaves         :   45 (6935 expanded)
%              Depth                    :   27
%              Number of atoms          :  698 (81227 expanded)
%              Number of equality atoms :  231 (28055 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_217,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_191,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_149,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_175,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_187,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_196,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_187])).

tff(c_201,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_196])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_455,plain,(
    ! [A_117,B_114,F_115,D_118,C_116,E_113] :
      ( k1_partfun1(A_117,B_114,C_116,D_118,E_113,F_115) = k5_relat_1(E_113,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_116,D_118)))
      | ~ v1_funct_1(F_115)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_117,B_114)))
      | ~ v1_funct_1(E_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_459,plain,(
    ! [A_117,B_114,E_113] :
      ( k1_partfun1(A_117,B_114,'#skF_2','#skF_1',E_113,'#skF_4') = k5_relat_1(E_113,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_117,B_114)))
      | ~ v1_funct_1(E_113) ) ),
    inference(resolution,[status(thm)],[c_76,c_455])).

tff(c_469,plain,(
    ! [A_119,B_120,E_121] :
      ( k1_partfun1(A_119,B_120,'#skF_2','#skF_1',E_121,'#skF_4') = k5_relat_1(E_121,'#skF_4')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_459])).

tff(c_478,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_469])).

tff(c_485,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_478])).

tff(c_44,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_320,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_relset_1(A_90,B_91,C_89,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_328,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_320])).

tff(c_343,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_328])).

tff(c_359,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_492,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_359])).

tff(c_673,plain,(
    ! [C_137,E_140,F_138,A_136,D_135,B_139] :
      ( m1_subset_1(k1_partfun1(A_136,B_139,C_137,D_135,E_140,F_138),k1_zfmisc_1(k2_zfmisc_1(A_136,D_135)))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_137,D_135)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_136,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_710,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_673])).

tff(c_732,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_710])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_732])).

tff(c_735,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_2099,plain,(
    ! [A_263,D_264,F_261,E_259,B_260,C_262] :
      ( k1_partfun1(A_263,B_260,C_262,D_264,E_259,F_261) = k5_relat_1(E_259,F_261)
      | ~ m1_subset_1(F_261,k1_zfmisc_1(k2_zfmisc_1(C_262,D_264)))
      | ~ v1_funct_1(F_261)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_263,B_260)))
      | ~ v1_funct_1(E_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2103,plain,(
    ! [A_263,B_260,E_259] :
      ( k1_partfun1(A_263,B_260,'#skF_2','#skF_1',E_259,'#skF_4') = k5_relat_1(E_259,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_263,B_260)))
      | ~ v1_funct_1(E_259) ) ),
    inference(resolution,[status(thm)],[c_76,c_2099])).

tff(c_2167,plain,(
    ! [A_267,B_268,E_269] :
      ( k1_partfun1(A_267,B_268,'#skF_2','#skF_1',E_269,'#skF_4') = k5_relat_1(E_269,'#skF_4')
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ v1_funct_1(E_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2103])).

tff(c_2176,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2167])).

tff(c_2183,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_735,c_2176])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_139,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_148,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_139])).

tff(c_157,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_148])).

tff(c_145,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_139])).

tff(c_154,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_20,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_1815,plain,(
    ! [C_225,A_224,E_228,D_223,B_227,F_226] :
      ( v1_funct_1(k1_partfun1(A_224,B_227,C_225,D_223,E_228,F_226))
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(C_225,D_223)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_224,B_227)))
      | ~ v1_funct_1(E_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1819,plain,(
    ! [A_224,B_227,E_228] :
      ( v1_funct_1(k1_partfun1(A_224,B_227,'#skF_2','#skF_1',E_228,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_224,B_227)))
      | ~ v1_funct_1(E_228) ) ),
    inference(resolution,[status(thm)],[c_76,c_1815])).

tff(c_1829,plain,(
    ! [A_229,B_230,E_231] :
      ( v1_funct_1(k1_partfun1(A_229,B_230,'#skF_2','#skF_1',E_231,'#skF_4'))
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_1(E_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1819])).

tff(c_1838,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1829])).

tff(c_1845,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_735,c_1838])).

tff(c_48,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [A_11] : k2_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_30,plain,(
    ! [A_15,B_17] :
      ( k2_funct_1(A_15) = B_17
      | k6_relat_1(k2_relat_1(A_15)) != k5_relat_1(B_17,A_15)
      | k2_relat_1(B_17) != k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_760,plain,(
    ! [A_143,B_144] :
      ( k2_funct_1(A_143) = B_144
      | k6_partfun1(k2_relat_1(A_143)) != k5_relat_1(B_144,A_143)
      | k2_relat_1(B_144) != k1_relat_1(A_143)
      | ~ v2_funct_1(A_143)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30])).

tff(c_762,plain,(
    ! [B_144] :
      ( k2_funct_1('#skF_3') = B_144
      | k5_relat_1(B_144,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_144) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_760])).

tff(c_771,plain,(
    ! [B_145] :
      ( k2_funct_1('#skF_3') = B_145
      | k5_relat_1(B_145,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_145) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86,c_70,c_762])).

tff(c_786,plain,(
    ! [A_13] :
      ( k6_partfun1(A_13) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_13),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_13)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_89,c_771])).

tff(c_797,plain,(
    ! [A_13] :
      ( k6_partfun1(A_13) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_13),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_13
      | ~ v1_funct_1(k6_partfun1(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_786])).

tff(c_1849,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1845,c_797])).

tff(c_1869,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1849])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    ! [A_11] : k1_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2000,plain,(
    ! [A_255,C_256,B_257] :
      ( k6_partfun1(A_255) = k5_relat_1(C_256,k2_funct_1(C_256))
      | k1_xboole_0 = B_257
      | ~ v2_funct_1(C_256)
      | k2_relset_1(A_255,B_257,C_256) != B_257
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_257)))
      | ~ v1_funct_2(C_256,A_255,B_257)
      | ~ v1_funct_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2006,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2000])).

tff(c_2016,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_2006])).

tff(c_2017,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2016])).

tff(c_28,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [A_79,B_80] :
      ( k1_relat_1(k5_relat_1(A_79,B_80)) = k1_relat_1(A_79)
      | ~ r1_tarski(k2_relat_1(A_79),k1_relat_1(B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,(
    ! [B_80] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_80)) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k1_relat_1(B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_206])).

tff(c_253,plain,(
    ! [B_84] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_84)) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k1_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_209])).

tff(c_259,plain,(
    ! [A_14] :
      ( k1_relat_1(k5_relat_1('#skF_3',k2_funct_1(A_14))) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k2_relat_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_253])).

tff(c_2021,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_259])).

tff(c_2025,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86,c_70,c_6,c_201,c_91,c_2021])).

tff(c_2026,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1869,c_2025])).

tff(c_2030,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2026])).

tff(c_2034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86,c_2030])).

tff(c_2036,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1849])).

tff(c_799,plain,(
    ! [B_150,C_148,E_151,F_149,D_146,A_147] :
      ( v1_funct_1(k1_partfun1(A_147,B_150,C_148,D_146,E_151,F_149))
      | ~ m1_subset_1(F_149,k1_zfmisc_1(k2_zfmisc_1(C_148,D_146)))
      | ~ v1_funct_1(F_149)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_147,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_803,plain,(
    ! [A_147,B_150,E_151] :
      ( v1_funct_1(k1_partfun1(A_147,B_150,'#skF_2','#skF_1',E_151,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_147,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(resolution,[status(thm)],[c_76,c_799])).

tff(c_814,plain,(
    ! [A_152,B_153,E_154] :
      ( v1_funct_1(k1_partfun1(A_152,B_153,'#skF_2','#skF_1',E_154,'#skF_4'))
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_1(E_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_803])).

tff(c_823,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_814])).

tff(c_830,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_735,c_823])).

tff(c_865,plain,(
    ! [A_166] :
      ( k6_partfun1(A_166) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_166),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_166
      | ~ v1_funct_1(k6_partfun1(A_166)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_786])).

tff(c_869,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_830,c_865])).

tff(c_870,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_901,plain,(
    ! [A_171,C_172,B_173] :
      ( k6_partfun1(A_171) = k5_relat_1(C_172,k2_funct_1(C_172))
      | k1_xboole_0 = B_173
      | ~ v2_funct_1(C_172)
      | k2_relset_1(A_171,B_173,C_172) != B_173
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_173)))
      | ~ v1_funct_2(C_172,A_171,B_173)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_907,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_901])).

tff(c_917,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_907])).

tff(c_918,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_917])).

tff(c_922,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_259])).

tff(c_926,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86,c_70,c_6,c_201,c_91,c_922])).

tff(c_927,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_870,c_926])).

tff(c_931,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_927])).

tff(c_935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86,c_931])).

tff(c_937,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_777,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_154,c_771])).

tff(c_792,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_777])).

tff(c_793,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_792])).

tff(c_798,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_793])).

tff(c_940,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_798])).

tff(c_176,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_183,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_44,c_176])).

tff(c_199,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_187])).

tff(c_1699,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k2_relset_1(A_216,B_217,C_218) = B_217
      | ~ r2_relset_1(B_217,B_217,k1_partfun1(B_217,A_216,A_216,B_217,D_219,C_218),k6_partfun1(B_217))
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(B_217,A_216)))
      | ~ v1_funct_2(D_219,B_217,A_216)
      | ~ v1_funct_1(D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_2(C_218,A_216,B_217)
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1705,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_1699])).

tff(c_1709,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_183,c_199,c_1705])).

tff(c_1711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1709])).

tff(c_1713,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_793])).

tff(c_1714,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1713,c_199])).

tff(c_2041,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_1714])).

tff(c_2243,plain,(
    ! [B_272,C_273,A_274] :
      ( k6_partfun1(B_272) = k5_relat_1(k2_funct_1(C_273),C_273)
      | k1_xboole_0 = B_272
      | ~ v2_funct_1(C_273)
      | k2_relset_1(A_274,B_272,C_273) != B_272
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_274,B_272)))
      | ~ v1_funct_2(C_273,A_274,B_272)
      | ~ v1_funct_1(C_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2247,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2243])).

tff(c_2255,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2041,c_2247])).

tff(c_2256,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2255])).

tff(c_2270,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2256])).

tff(c_24,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_2836,plain,(
    ! [B_301,A_303,E_302,D_299,C_300] :
      ( k1_xboole_0 = C_300
      | v2_funct_1(E_302)
      | k2_relset_1(A_303,B_301,D_299) != B_301
      | ~ v2_funct_1(k1_partfun1(A_303,B_301,B_301,C_300,D_299,E_302))
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(B_301,C_300)))
      | ~ v1_funct_2(E_302,B_301,C_300)
      | ~ v1_funct_1(E_302)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1(A_303,B_301)))
      | ~ v1_funct_2(D_299,A_303,B_301)
      | ~ v1_funct_1(D_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2842,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_2836])).

tff(c_2850,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_88,c_74,c_2842])).

tff(c_2852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2270,c_68,c_2850])).

tff(c_2854,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2256])).

tff(c_2853,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2256])).

tff(c_26,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5461,plain,(
    ! [A_415,B_416] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_415),B_416)) = k1_relat_1(k2_funct_1(A_415))
      | ~ r1_tarski(k1_relat_1(A_415),k1_relat_1(B_416))
      | ~ v1_relat_1(B_416)
      | ~ v1_relat_1(k2_funct_1(A_415))
      | ~ v2_funct_1(A_415)
      | ~ v1_funct_1(A_415)
      | ~ v1_relat_1(A_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_19021,plain,(
    ! [A_781] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_781),A_781)) = k1_relat_1(k2_funct_1(A_781))
      | ~ v1_relat_1(k2_funct_1(A_781))
      | ~ v2_funct_1(A_781)
      | ~ v1_funct_1(A_781)
      | ~ v1_relat_1(A_781) ) ),
    inference(resolution,[status(thm)],[c_6,c_5461])).

tff(c_19068,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2853,c_19021])).

tff(c_19095,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_2854,c_91,c_19068])).

tff(c_19140,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_19095])).

tff(c_19143,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_19140])).

tff(c_19147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_19143])).

tff(c_19149,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_19095])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_768,plain,(
    ! [B_144] :
      ( k2_funct_1('#skF_3') = B_144
      | k5_relat_1(B_144,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_144) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86,c_70,c_762])).

tff(c_2043,plain,(
    ! [B_144] :
      ( k2_funct_1('#skF_3') = B_144
      | k5_relat_1(B_144,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_144) != '#skF_1'
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_768])).

tff(c_19154,plain,
    ( k2_funct_1('#skF_3') = k2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19149,c_2043])).

tff(c_26246,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_19154])).

tff(c_26447,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_26246])).

tff(c_26451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_26447])).

tff(c_26453,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_19154])).

tff(c_2922,plain,(
    ! [A_308,C_309,B_310] :
      ( k6_partfun1(A_308) = k5_relat_1(C_309,k2_funct_1(C_309))
      | k1_xboole_0 = B_310
      | ~ v2_funct_1(C_309)
      | k2_relset_1(A_308,B_310,C_309) != B_310
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_308,B_310)))
      | ~ v1_funct_2(C_309,A_308,B_310)
      | ~ v1_funct_1(C_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2926,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2922])).

tff(c_2934,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2041,c_2854,c_2926])).

tff(c_2935,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2934])).

tff(c_4139,plain,(
    ! [A_359,A_360] :
      ( k1_relat_1(k5_relat_1(A_359,k2_funct_1(A_360))) = k1_relat_1(A_359)
      | ~ r1_tarski(k2_relat_1(A_359),k2_relat_1(A_360))
      | ~ v1_relat_1(k2_funct_1(A_360))
      | ~ v1_relat_1(A_359)
      | ~ v2_funct_1(A_360)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_206])).

tff(c_5389,plain,(
    ! [A_414] :
      ( k1_relat_1(k5_relat_1(A_414,k2_funct_1(A_414))) = k1_relat_1(A_414)
      | ~ v1_relat_1(k2_funct_1(A_414))
      | ~ v2_funct_1(A_414)
      | ~ v1_funct_1(A_414)
      | ~ v1_relat_1(A_414) ) ),
    inference(resolution,[status(thm)],[c_6,c_4139])).

tff(c_5419,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2935,c_5389])).

tff(c_5436,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_2854,c_91,c_5419])).

tff(c_5441,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5436])).

tff(c_5444,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_5441])).

tff(c_5448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_5444])).

tff(c_5449,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5436])).

tff(c_5069,plain,(
    ! [A_399] :
      ( k1_relat_1(k5_relat_1(A_399,k2_funct_1(A_399))) = k1_relat_1(A_399)
      | ~ v1_relat_1(k2_funct_1(A_399))
      | ~ v2_funct_1(A_399)
      | ~ v1_funct_1(A_399)
      | ~ v1_relat_1(A_399) ) ),
    inference(resolution,[status(thm)],[c_6,c_4139])).

tff(c_5113,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2935,c_5069])).

tff(c_5134,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_2854,c_91,c_5113])).

tff(c_5139,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5134])).

tff(c_5214,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_5139])).

tff(c_5218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_5214])).

tff(c_5219,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5134])).

tff(c_2105,plain,(
    ! [A_263,B_260,E_259] :
      ( k1_partfun1(A_263,B_260,'#skF_1','#skF_2',E_259,'#skF_3') = k5_relat_1(E_259,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_263,B_260)))
      | ~ v1_funct_1(E_259) ) ),
    inference(resolution,[status(thm)],[c_82,c_2099])).

tff(c_2895,plain,(
    ! [A_305,B_306,E_307] :
      ( k1_partfun1(A_305,B_306,'#skF_1','#skF_2',E_307,'#skF_3') = k5_relat_1(E_307,'#skF_3')
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(E_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2105])).

tff(c_2901,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2895])).

tff(c_2908,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2901])).

tff(c_3001,plain,(
    ! [A_315,E_319,C_316,B_318,D_314,F_317] :
      ( m1_subset_1(k1_partfun1(A_315,B_318,C_316,D_314,E_319,F_317),k1_zfmisc_1(k2_zfmisc_1(A_315,D_314)))
      | ~ m1_subset_1(F_317,k1_zfmisc_1(k2_zfmisc_1(C_316,D_314)))
      | ~ v1_funct_1(F_317)
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(A_315,B_318)))
      | ~ v1_funct_1(E_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3041,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2908,c_3001])).

tff(c_3068,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_86,c_82,c_3041])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3165,plain,
    ( v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3068,c_8])).

tff(c_3196,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3165])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( k1_relat_1(k5_relat_1(A_8,B_10)) = k1_relat_1(A_8)
      | ~ r1_tarski(k2_relat_1(A_8),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1720,plain,(
    ! [B_10] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_10)) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_12])).

tff(c_1733,plain,(
    ! [B_220] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_220)) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_220))
      | ~ v1_relat_1(B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1720])).

tff(c_1758,plain,
    ( k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1733])).

tff(c_1769,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1758])).

tff(c_223,plain,(
    ! [B_80] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_80)) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_209])).

tff(c_2138,plain,(
    ! [B_266] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_266)) = '#skF_1'
      | ~ r1_tarski('#skF_2',k1_relat_1(B_266))
      | ~ v1_relat_1(B_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_223])).

tff(c_2150,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k5_relat_1('#skF_4','#skF_3'))) = '#skF_1'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1769,c_2138])).

tff(c_4196,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k5_relat_1('#skF_4','#skF_3'))) = '#skF_1'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3196,c_2150])).

tff(c_4197,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4196])).

tff(c_5221,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5219,c_4197])).

tff(c_5227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5221])).

tff(c_5229,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4196])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5238,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5229,c_2])).

tff(c_5256,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5238])).

tff(c_5451,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5449,c_5256])).

tff(c_5458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5451])).

tff(c_5459,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5238])).

tff(c_2042,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_1713])).

tff(c_87,plain,(
    ! [A_15,B_17] :
      ( k2_funct_1(A_15) = B_17
      | k6_partfun1(k2_relat_1(A_15)) != k5_relat_1(B_17,A_15)
      | k2_relat_1(B_17) != k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30])).

tff(c_2060,plain,(
    ! [B_17] :
      ( k2_funct_1('#skF_4') = B_17
      | k5_relat_1(B_17,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_17) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2042,c_87])).

tff(c_2067,plain,(
    ! [B_17] :
      ( k2_funct_1('#skF_4') = B_17
      | k5_relat_1(B_17,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_17) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_2060])).

tff(c_75591,plain,(
    ! [B_1548] :
      ( k2_funct_1('#skF_4') = B_1548
      | k5_relat_1(B_1548,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1548) != '#skF_2'
      | ~ v1_funct_1(B_1548)
      | ~ v1_relat_1(B_1548) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2854,c_5459,c_2067])).

tff(c_76506,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_75591])).

tff(c_77282,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_201,c_2183,c_76506])).

tff(c_19148,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19095])).

tff(c_17833,plain,(
    ! [A_746,B_747] :
      ( k2_funct_1(k2_funct_1(A_746)) = B_747
      | k5_relat_1(B_747,k2_funct_1(A_746)) != k6_partfun1(k1_relat_1(A_746))
      | k2_relat_1(B_747) != k1_relat_1(k2_funct_1(A_746))
      | ~ v2_funct_1(k2_funct_1(A_746))
      | ~ v1_funct_1(B_747)
      | ~ v1_relat_1(B_747)
      | ~ v1_funct_1(k2_funct_1(A_746))
      | ~ v1_relat_1(k2_funct_1(A_746))
      | ~ v2_funct_1(A_746)
      | ~ v1_funct_1(A_746)
      | ~ v1_relat_1(A_746) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_760])).

tff(c_17835,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k1_relat_1('#skF_4')) != k6_partfun1('#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2935,c_17833])).

tff(c_17839,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_80,c_2854,c_154,c_80,c_2042,c_5459,c_17835])).

tff(c_27000,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19149,c_26453,c_19148,c_17839])).

tff(c_27001,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_27000])).

tff(c_77616,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77282,c_27001])).

tff(c_77626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_77616])).

tff(c_77628,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_27000])).

tff(c_77627,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_27000])).

tff(c_764,plain,(
    ! [A_14,B_144] :
      ( k2_funct_1(k2_funct_1(A_14)) = B_144
      | k5_relat_1(B_144,k2_funct_1(A_14)) != k6_partfun1(k1_relat_1(A_14))
      | k2_relat_1(B_144) != k1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_760])).

tff(c_77664,plain,(
    ! [B_144] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) = B_144
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_144,'#skF_4')
      | k2_relat_1(B_144) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77627,c_764])).

tff(c_78233,plain,(
    ! [B_1571] :
      ( k2_funct_1('#skF_4') = B_1571
      | k5_relat_1(B_1571,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1571) != '#skF_2'
      | ~ v1_funct_1(B_1571)
      | ~ v1_relat_1(B_1571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19149,c_26453,c_77628,c_154,c_77627,c_80,c_77627,c_2854,c_77627,c_5459,c_77627,c_19148,c_77627,c_77664])).

tff(c_78485,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_78233])).

tff(c_78704,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_201,c_2183,c_78485])).

tff(c_78715,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78704,c_77627])).

tff(c_78726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_78715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:26:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 57.28/46.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.46/46.89  
% 57.46/46.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.46/46.89  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 57.46/46.89  
% 57.46/46.89  %Foreground sorts:
% 57.46/46.89  
% 57.46/46.89  
% 57.46/46.89  %Background operators:
% 57.46/46.89  
% 57.46/46.89  
% 57.46/46.89  %Foreground operators:
% 57.46/46.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 57.46/46.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 57.46/46.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 57.46/46.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 57.46/46.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 57.46/46.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 57.46/46.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 57.46/46.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 57.46/46.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 57.46/46.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 57.46/46.89  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 57.46/46.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 57.46/46.89  tff('#skF_2', type, '#skF_2': $i).
% 57.46/46.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 57.46/46.89  tff('#skF_3', type, '#skF_3': $i).
% 57.46/46.89  tff('#skF_1', type, '#skF_1': $i).
% 57.46/46.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 57.46/46.89  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 57.46/46.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 57.46/46.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 57.46/46.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 57.46/46.89  tff('#skF_4', type, '#skF_4': $i).
% 57.46/46.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 57.46/46.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 57.46/46.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 57.46/46.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 57.46/46.89  
% 57.63/46.93  tff(f_217, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 57.63/46.93  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 57.63/46.93  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 57.63/46.93  tff(f_120, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 57.63/46.93  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 57.63/46.93  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 57.63/46.93  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 57.63/46.93  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 57.63/46.93  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 57.63/46.93  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 57.63/46.93  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 57.63/46.93  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 57.63/46.93  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 57.63/46.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 57.63/46.93  tff(f_191, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 57.63/46.93  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 57.63/46.93  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 57.63/46.93  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 57.63/46.93  tff(f_175, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 57.63/46.93  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_187, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 57.63/46.93  tff(c_196, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_187])).
% 57.63/46.93  tff(c_201, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_196])).
% 57.63/46.93  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_455, plain, (![A_117, B_114, F_115, D_118, C_116, E_113]: (k1_partfun1(A_117, B_114, C_116, D_118, E_113, F_115)=k5_relat_1(E_113, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_116, D_118))) | ~v1_funct_1(F_115) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_117, B_114))) | ~v1_funct_1(E_113))), inference(cnfTransformation, [status(thm)], [f_130])).
% 57.63/46.93  tff(c_459, plain, (![A_117, B_114, E_113]: (k1_partfun1(A_117, B_114, '#skF_2', '#skF_1', E_113, '#skF_4')=k5_relat_1(E_113, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_117, B_114))) | ~v1_funct_1(E_113))), inference(resolution, [status(thm)], [c_76, c_455])).
% 57.63/46.93  tff(c_469, plain, (![A_119, B_120, E_121]: (k1_partfun1(A_119, B_120, '#skF_2', '#skF_1', E_121, '#skF_4')=k5_relat_1(E_121, '#skF_4') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_121))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_459])).
% 57.63/46.93  tff(c_478, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_469])).
% 57.63/46.93  tff(c_485, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_478])).
% 57.63/46.93  tff(c_44, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 57.63/46.93  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_320, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_relset_1(A_90, B_91, C_89, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 57.63/46.93  tff(c_328, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_320])).
% 57.63/46.93  tff(c_343, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_328])).
% 57.63/46.93  tff(c_359, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_343])).
% 57.63/46.93  tff(c_492, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_359])).
% 57.63/46.93  tff(c_673, plain, (![C_137, E_140, F_138, A_136, D_135, B_139]: (m1_subset_1(k1_partfun1(A_136, B_139, C_137, D_135, E_140, F_138), k1_zfmisc_1(k2_zfmisc_1(A_136, D_135))) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_137, D_135))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_136, B_139))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_116])).
% 57.63/46.93  tff(c_710, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_485, c_673])).
% 57.63/46.93  tff(c_732, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_710])).
% 57.63/46.93  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_732])).
% 57.63/46.93  tff(c_735, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_343])).
% 57.63/46.93  tff(c_2099, plain, (![A_263, D_264, F_261, E_259, B_260, C_262]: (k1_partfun1(A_263, B_260, C_262, D_264, E_259, F_261)=k5_relat_1(E_259, F_261) | ~m1_subset_1(F_261, k1_zfmisc_1(k2_zfmisc_1(C_262, D_264))) | ~v1_funct_1(F_261) | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_263, B_260))) | ~v1_funct_1(E_259))), inference(cnfTransformation, [status(thm)], [f_130])).
% 57.63/46.93  tff(c_2103, plain, (![A_263, B_260, E_259]: (k1_partfun1(A_263, B_260, '#skF_2', '#skF_1', E_259, '#skF_4')=k5_relat_1(E_259, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_263, B_260))) | ~v1_funct_1(E_259))), inference(resolution, [status(thm)], [c_76, c_2099])).
% 57.63/46.93  tff(c_2167, plain, (![A_267, B_268, E_269]: (k1_partfun1(A_267, B_268, '#skF_2', '#skF_1', E_269, '#skF_4')=k5_relat_1(E_269, '#skF_4') | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~v1_funct_1(E_269))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2103])).
% 57.63/46.93  tff(c_2176, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2167])).
% 57.63/46.93  tff(c_2183, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_735, c_2176])).
% 57.63/46.93  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 57.63/46.93  tff(c_139, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 57.63/46.93  tff(c_148, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_139])).
% 57.63/46.93  tff(c_157, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_148])).
% 57.63/46.93  tff(c_145, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_139])).
% 57.63/46.93  tff(c_154, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_145])).
% 57.63/46.93  tff(c_20, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 57.63/46.93  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_1815, plain, (![C_225, A_224, E_228, D_223, B_227, F_226]: (v1_funct_1(k1_partfun1(A_224, B_227, C_225, D_223, E_228, F_226)) | ~m1_subset_1(F_226, k1_zfmisc_1(k2_zfmisc_1(C_225, D_223))) | ~v1_funct_1(F_226) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_224, B_227))) | ~v1_funct_1(E_228))), inference(cnfTransformation, [status(thm)], [f_116])).
% 57.63/46.93  tff(c_1819, plain, (![A_224, B_227, E_228]: (v1_funct_1(k1_partfun1(A_224, B_227, '#skF_2', '#skF_1', E_228, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_224, B_227))) | ~v1_funct_1(E_228))), inference(resolution, [status(thm)], [c_76, c_1815])).
% 57.63/46.93  tff(c_1829, plain, (![A_229, B_230, E_231]: (v1_funct_1(k1_partfun1(A_229, B_230, '#skF_2', '#skF_1', E_231, '#skF_4')) | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_1(E_231))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1819])).
% 57.63/46.93  tff(c_1838, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1829])).
% 57.63/46.93  tff(c_1845, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_735, c_1838])).
% 57.63/46.93  tff(c_48, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_132])).
% 57.63/46.93  tff(c_16, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 57.63/46.93  tff(c_90, plain, (![A_11]: (k2_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 57.63/46.93  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 57.63/46.93  tff(c_89, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 57.63/46.93  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_30, plain, (![A_15, B_17]: (k2_funct_1(A_15)=B_17 | k6_relat_1(k2_relat_1(A_15))!=k5_relat_1(B_17, A_15) | k2_relat_1(B_17)!=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 57.63/46.93  tff(c_760, plain, (![A_143, B_144]: (k2_funct_1(A_143)=B_144 | k6_partfun1(k2_relat_1(A_143))!=k5_relat_1(B_144, A_143) | k2_relat_1(B_144)!=k1_relat_1(A_143) | ~v2_funct_1(A_143) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30])).
% 57.63/46.93  tff(c_762, plain, (![B_144]: (k2_funct_1('#skF_3')=B_144 | k5_relat_1(B_144, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_144)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_760])).
% 57.63/46.93  tff(c_771, plain, (![B_145]: (k2_funct_1('#skF_3')=B_145 | k5_relat_1(B_145, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_145)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_86, c_70, c_762])).
% 57.63/46.93  tff(c_786, plain, (![A_13]: (k6_partfun1(A_13)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_13), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_13))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_13)))), inference(resolution, [status(thm)], [c_89, c_771])).
% 57.63/46.93  tff(c_797, plain, (![A_13]: (k6_partfun1(A_13)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_13), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_13 | ~v1_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_786])).
% 57.63/46.93  tff(c_1849, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_1845, c_797])).
% 57.63/46.93  tff(c_1869, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1849])).
% 57.63/46.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 57.63/46.93  tff(c_14, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 57.63/46.93  tff(c_91, plain, (![A_11]: (k1_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 57.63/46.93  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 57.63/46.93  tff(c_2000, plain, (![A_255, C_256, B_257]: (k6_partfun1(A_255)=k5_relat_1(C_256, k2_funct_1(C_256)) | k1_xboole_0=B_257 | ~v2_funct_1(C_256) | k2_relset_1(A_255, B_257, C_256)!=B_257 | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_257))) | ~v1_funct_2(C_256, A_255, B_257) | ~v1_funct_1(C_256))), inference(cnfTransformation, [status(thm)], [f_191])).
% 57.63/46.93  tff(c_2006, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2000])).
% 57.63/46.93  tff(c_2016, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_2006])).
% 57.63/46.93  tff(c_2017, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_2016])).
% 57.63/46.93  tff(c_28, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 57.63/46.93  tff(c_206, plain, (![A_79, B_80]: (k1_relat_1(k5_relat_1(A_79, B_80))=k1_relat_1(A_79) | ~r1_tarski(k2_relat_1(A_79), k1_relat_1(B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 57.63/46.93  tff(c_209, plain, (![B_80]: (k1_relat_1(k5_relat_1('#skF_3', B_80))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k1_relat_1(B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_206])).
% 57.63/46.93  tff(c_253, plain, (![B_84]: (k1_relat_1(k5_relat_1('#skF_3', B_84))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k1_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_209])).
% 57.63/46.93  tff(c_259, plain, (![A_14]: (k1_relat_1(k5_relat_1('#skF_3', k2_funct_1(A_14)))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k2_relat_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_28, c_253])).
% 57.63/46.93  tff(c_2021, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2017, c_259])).
% 57.63/46.93  tff(c_2025, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_86, c_70, c_6, c_201, c_91, c_2021])).
% 57.63/46.93  tff(c_2026, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1869, c_2025])).
% 57.63/46.93  tff(c_2030, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2026])).
% 57.63/46.93  tff(c_2034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_86, c_2030])).
% 57.63/46.93  tff(c_2036, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1849])).
% 57.63/46.93  tff(c_799, plain, (![B_150, C_148, E_151, F_149, D_146, A_147]: (v1_funct_1(k1_partfun1(A_147, B_150, C_148, D_146, E_151, F_149)) | ~m1_subset_1(F_149, k1_zfmisc_1(k2_zfmisc_1(C_148, D_146))) | ~v1_funct_1(F_149) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_147, B_150))) | ~v1_funct_1(E_151))), inference(cnfTransformation, [status(thm)], [f_116])).
% 57.63/46.93  tff(c_803, plain, (![A_147, B_150, E_151]: (v1_funct_1(k1_partfun1(A_147, B_150, '#skF_2', '#skF_1', E_151, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_147, B_150))) | ~v1_funct_1(E_151))), inference(resolution, [status(thm)], [c_76, c_799])).
% 57.63/46.93  tff(c_814, plain, (![A_152, B_153, E_154]: (v1_funct_1(k1_partfun1(A_152, B_153, '#skF_2', '#skF_1', E_154, '#skF_4')) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_1(E_154))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_803])).
% 57.63/46.93  tff(c_823, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_814])).
% 57.63/46.93  tff(c_830, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_735, c_823])).
% 57.63/46.93  tff(c_865, plain, (![A_166]: (k6_partfun1(A_166)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_166), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_166 | ~v1_funct_1(k6_partfun1(A_166)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_786])).
% 57.63/46.93  tff(c_869, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_830, c_865])).
% 57.63/46.93  tff(c_870, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_869])).
% 57.63/46.93  tff(c_901, plain, (![A_171, C_172, B_173]: (k6_partfun1(A_171)=k5_relat_1(C_172, k2_funct_1(C_172)) | k1_xboole_0=B_173 | ~v2_funct_1(C_172) | k2_relset_1(A_171, B_173, C_172)!=B_173 | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_173))) | ~v1_funct_2(C_172, A_171, B_173) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_191])).
% 57.63/46.93  tff(c_907, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_901])).
% 57.63/46.93  tff(c_917, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_907])).
% 57.63/46.93  tff(c_918, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_917])).
% 57.63/46.93  tff(c_922, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_918, c_259])).
% 57.63/46.93  tff(c_926, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_86, c_70, c_6, c_201, c_91, c_922])).
% 57.63/46.93  tff(c_927, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_870, c_926])).
% 57.63/46.93  tff(c_931, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_927])).
% 57.63/46.93  tff(c_935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_86, c_931])).
% 57.63/46.93  tff(c_937, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_869])).
% 57.63/46.93  tff(c_777, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_154, c_771])).
% 57.63/46.93  tff(c_792, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_777])).
% 57.63/46.93  tff(c_793, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_792])).
% 57.63/46.93  tff(c_798, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_793])).
% 57.63/46.93  tff(c_940, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_937, c_798])).
% 57.63/46.93  tff(c_176, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 57.63/46.93  tff(c_183, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_44, c_176])).
% 57.63/46.93  tff(c_199, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_187])).
% 57.63/46.93  tff(c_1699, plain, (![A_216, B_217, C_218, D_219]: (k2_relset_1(A_216, B_217, C_218)=B_217 | ~r2_relset_1(B_217, B_217, k1_partfun1(B_217, A_216, A_216, B_217, D_219, C_218), k6_partfun1(B_217)) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(B_217, A_216))) | ~v1_funct_2(D_219, B_217, A_216) | ~v1_funct_1(D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_2(C_218, A_216, B_217) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_149])).
% 57.63/46.93  tff(c_1705, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_735, c_1699])).
% 57.63/46.93  tff(c_1709, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_183, c_199, c_1705])).
% 57.63/46.93  tff(c_1711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_940, c_1709])).
% 57.63/46.93  tff(c_1713, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_793])).
% 57.63/46.93  tff(c_1714, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1713, c_199])).
% 57.63/46.93  tff(c_2041, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_1714])).
% 57.63/46.93  tff(c_2243, plain, (![B_272, C_273, A_274]: (k6_partfun1(B_272)=k5_relat_1(k2_funct_1(C_273), C_273) | k1_xboole_0=B_272 | ~v2_funct_1(C_273) | k2_relset_1(A_274, B_272, C_273)!=B_272 | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_274, B_272))) | ~v1_funct_2(C_273, A_274, B_272) | ~v1_funct_1(C_273))), inference(cnfTransformation, [status(thm)], [f_191])).
% 57.63/46.93  tff(c_2247, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2243])).
% 57.63/46.93  tff(c_2255, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2041, c_2247])).
% 57.63/46.93  tff(c_2256, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_2255])).
% 57.63/46.93  tff(c_2270, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2256])).
% 57.63/46.93  tff(c_24, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 57.63/46.93  tff(c_88, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 57.63/46.93  tff(c_2836, plain, (![B_301, A_303, E_302, D_299, C_300]: (k1_xboole_0=C_300 | v2_funct_1(E_302) | k2_relset_1(A_303, B_301, D_299)!=B_301 | ~v2_funct_1(k1_partfun1(A_303, B_301, B_301, C_300, D_299, E_302)) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(B_301, C_300))) | ~v1_funct_2(E_302, B_301, C_300) | ~v1_funct_1(E_302) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1(A_303, B_301))) | ~v1_funct_2(D_299, A_303, B_301) | ~v1_funct_1(D_299))), inference(cnfTransformation, [status(thm)], [f_175])).
% 57.63/46.93  tff(c_2842, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_735, c_2836])).
% 57.63/46.93  tff(c_2850, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_88, c_74, c_2842])).
% 57.63/46.93  tff(c_2852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2270, c_68, c_2850])).
% 57.63/46.93  tff(c_2854, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2256])).
% 57.63/46.93  tff(c_2853, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2256])).
% 57.63/46.93  tff(c_26, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 57.63/46.93  tff(c_5461, plain, (![A_415, B_416]: (k1_relat_1(k5_relat_1(k2_funct_1(A_415), B_416))=k1_relat_1(k2_funct_1(A_415)) | ~r1_tarski(k1_relat_1(A_415), k1_relat_1(B_416)) | ~v1_relat_1(B_416) | ~v1_relat_1(k2_funct_1(A_415)) | ~v2_funct_1(A_415) | ~v1_funct_1(A_415) | ~v1_relat_1(A_415))), inference(superposition, [status(thm), theory('equality')], [c_26, c_206])).
% 57.63/46.93  tff(c_19021, plain, (![A_781]: (k1_relat_1(k5_relat_1(k2_funct_1(A_781), A_781))=k1_relat_1(k2_funct_1(A_781)) | ~v1_relat_1(k2_funct_1(A_781)) | ~v2_funct_1(A_781) | ~v1_funct_1(A_781) | ~v1_relat_1(A_781))), inference(resolution, [status(thm)], [c_6, c_5461])).
% 57.63/46.93  tff(c_19068, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2853, c_19021])).
% 57.63/46.93  tff(c_19095, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_2854, c_91, c_19068])).
% 57.63/46.93  tff(c_19140, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_19095])).
% 57.63/46.93  tff(c_19143, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_19140])).
% 57.63/46.93  tff(c_19147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_19143])).
% 57.63/46.93  tff(c_19149, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_19095])).
% 57.63/46.93  tff(c_18, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 57.63/46.93  tff(c_768, plain, (![B_144]: (k2_funct_1('#skF_3')=B_144 | k5_relat_1(B_144, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_144)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_86, c_70, c_762])).
% 57.63/46.93  tff(c_2043, plain, (![B_144]: (k2_funct_1('#skF_3')=B_144 | k5_relat_1(B_144, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_144)!='#skF_1' | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_768])).
% 57.63/46.93  tff(c_19154, plain, (k2_funct_1('#skF_3')=k2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_19149, c_2043])).
% 57.63/46.93  tff(c_26246, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_19154])).
% 57.63/46.93  tff(c_26447, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_26246])).
% 57.63/46.93  tff(c_26451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_26447])).
% 57.63/46.93  tff(c_26453, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_19154])).
% 57.63/46.93  tff(c_2922, plain, (![A_308, C_309, B_310]: (k6_partfun1(A_308)=k5_relat_1(C_309, k2_funct_1(C_309)) | k1_xboole_0=B_310 | ~v2_funct_1(C_309) | k2_relset_1(A_308, B_310, C_309)!=B_310 | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_308, B_310))) | ~v1_funct_2(C_309, A_308, B_310) | ~v1_funct_1(C_309))), inference(cnfTransformation, [status(thm)], [f_191])).
% 57.63/46.93  tff(c_2926, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2922])).
% 57.63/46.93  tff(c_2934, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2041, c_2854, c_2926])).
% 57.63/46.93  tff(c_2935, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_2934])).
% 57.63/46.93  tff(c_4139, plain, (![A_359, A_360]: (k1_relat_1(k5_relat_1(A_359, k2_funct_1(A_360)))=k1_relat_1(A_359) | ~r1_tarski(k2_relat_1(A_359), k2_relat_1(A_360)) | ~v1_relat_1(k2_funct_1(A_360)) | ~v1_relat_1(A_359) | ~v2_funct_1(A_360) | ~v1_funct_1(A_360) | ~v1_relat_1(A_360))), inference(superposition, [status(thm), theory('equality')], [c_28, c_206])).
% 57.63/46.93  tff(c_5389, plain, (![A_414]: (k1_relat_1(k5_relat_1(A_414, k2_funct_1(A_414)))=k1_relat_1(A_414) | ~v1_relat_1(k2_funct_1(A_414)) | ~v2_funct_1(A_414) | ~v1_funct_1(A_414) | ~v1_relat_1(A_414))), inference(resolution, [status(thm)], [c_6, c_4139])).
% 57.63/46.93  tff(c_5419, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2935, c_5389])).
% 57.63/46.93  tff(c_5436, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_2854, c_91, c_5419])).
% 57.63/46.93  tff(c_5441, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5436])).
% 57.63/46.93  tff(c_5444, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_5441])).
% 57.63/46.93  tff(c_5448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_5444])).
% 57.63/46.93  tff(c_5449, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_5436])).
% 57.63/46.93  tff(c_5069, plain, (![A_399]: (k1_relat_1(k5_relat_1(A_399, k2_funct_1(A_399)))=k1_relat_1(A_399) | ~v1_relat_1(k2_funct_1(A_399)) | ~v2_funct_1(A_399) | ~v1_funct_1(A_399) | ~v1_relat_1(A_399))), inference(resolution, [status(thm)], [c_6, c_4139])).
% 57.63/46.93  tff(c_5113, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2935, c_5069])).
% 57.63/46.93  tff(c_5134, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_2854, c_91, c_5113])).
% 57.63/46.93  tff(c_5139, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5134])).
% 57.63/46.93  tff(c_5214, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_5139])).
% 57.63/46.93  tff(c_5218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_5214])).
% 57.63/46.93  tff(c_5219, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_5134])).
% 57.63/46.93  tff(c_2105, plain, (![A_263, B_260, E_259]: (k1_partfun1(A_263, B_260, '#skF_1', '#skF_2', E_259, '#skF_3')=k5_relat_1(E_259, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_263, B_260))) | ~v1_funct_1(E_259))), inference(resolution, [status(thm)], [c_82, c_2099])).
% 57.63/46.93  tff(c_2895, plain, (![A_305, B_306, E_307]: (k1_partfun1(A_305, B_306, '#skF_1', '#skF_2', E_307, '#skF_3')=k5_relat_1(E_307, '#skF_3') | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(E_307))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2105])).
% 57.63/46.93  tff(c_2901, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2895])).
% 57.63/46.93  tff(c_2908, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2901])).
% 57.63/46.93  tff(c_3001, plain, (![A_315, E_319, C_316, B_318, D_314, F_317]: (m1_subset_1(k1_partfun1(A_315, B_318, C_316, D_314, E_319, F_317), k1_zfmisc_1(k2_zfmisc_1(A_315, D_314))) | ~m1_subset_1(F_317, k1_zfmisc_1(k2_zfmisc_1(C_316, D_314))) | ~v1_funct_1(F_317) | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(A_315, B_318))) | ~v1_funct_1(E_319))), inference(cnfTransformation, [status(thm)], [f_116])).
% 57.63/46.93  tff(c_3041, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2908, c_3001])).
% 57.63/46.93  tff(c_3068, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_86, c_82, c_3041])).
% 57.63/46.93  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 57.63/46.93  tff(c_3165, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_3068, c_8])).
% 57.63/46.93  tff(c_3196, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3165])).
% 57.63/46.93  tff(c_12, plain, (![A_8, B_10]: (k1_relat_1(k5_relat_1(A_8, B_10))=k1_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), k1_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 57.63/46.93  tff(c_1720, plain, (![B_10]: (k1_relat_1(k5_relat_1('#skF_4', B_10))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1713, c_12])).
% 57.63/46.93  tff(c_1733, plain, (![B_220]: (k1_relat_1(k5_relat_1('#skF_4', B_220))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_220)) | ~v1_relat_1(B_220))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1720])).
% 57.63/46.93  tff(c_1758, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1733])).
% 57.63/46.93  tff(c_1769, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1758])).
% 57.63/46.93  tff(c_223, plain, (![B_80]: (k1_relat_1(k5_relat_1('#skF_3', B_80))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_209])).
% 57.63/46.93  tff(c_2138, plain, (![B_266]: (k1_relat_1(k5_relat_1('#skF_3', B_266))='#skF_1' | ~r1_tarski('#skF_2', k1_relat_1(B_266)) | ~v1_relat_1(B_266))), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_223])).
% 57.63/46.93  tff(c_2150, plain, (k1_relat_1(k5_relat_1('#skF_3', k5_relat_1('#skF_4', '#skF_3')))='#skF_1' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1769, c_2138])).
% 57.63/46.93  tff(c_4196, plain, (k1_relat_1(k5_relat_1('#skF_3', k5_relat_1('#skF_4', '#skF_3')))='#skF_1' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3196, c_2150])).
% 57.63/46.93  tff(c_4197, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4196])).
% 57.63/46.93  tff(c_5221, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5219, c_4197])).
% 57.63/46.93  tff(c_5227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5221])).
% 57.63/46.93  tff(c_5229, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4196])).
% 57.63/46.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 57.63/46.93  tff(c_5238, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_5229, c_2])).
% 57.63/46.93  tff(c_5256, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_5238])).
% 57.63/46.93  tff(c_5451, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5449, c_5256])).
% 57.63/46.93  tff(c_5458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5451])).
% 57.63/46.93  tff(c_5459, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_5238])).
% 57.63/46.93  tff(c_2042, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_1713])).
% 57.63/46.93  tff(c_87, plain, (![A_15, B_17]: (k2_funct_1(A_15)=B_17 | k6_partfun1(k2_relat_1(A_15))!=k5_relat_1(B_17, A_15) | k2_relat_1(B_17)!=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30])).
% 57.63/46.93  tff(c_2060, plain, (![B_17]: (k2_funct_1('#skF_4')=B_17 | k5_relat_1(B_17, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_17)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2042, c_87])).
% 57.63/46.93  tff(c_2067, plain, (![B_17]: (k2_funct_1('#skF_4')=B_17 | k5_relat_1(B_17, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_17)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_2060])).
% 57.63/46.93  tff(c_75591, plain, (![B_1548]: (k2_funct_1('#skF_4')=B_1548 | k5_relat_1(B_1548, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1548)!='#skF_2' | ~v1_funct_1(B_1548) | ~v1_relat_1(B_1548))), inference(demodulation, [status(thm), theory('equality')], [c_2854, c_5459, c_2067])).
% 57.63/46.93  tff(c_76506, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_157, c_75591])).
% 57.63/46.93  tff(c_77282, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_201, c_2183, c_76506])).
% 57.63/46.93  tff(c_19148, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(splitRight, [status(thm)], [c_19095])).
% 57.63/46.93  tff(c_17833, plain, (![A_746, B_747]: (k2_funct_1(k2_funct_1(A_746))=B_747 | k5_relat_1(B_747, k2_funct_1(A_746))!=k6_partfun1(k1_relat_1(A_746)) | k2_relat_1(B_747)!=k1_relat_1(k2_funct_1(A_746)) | ~v2_funct_1(k2_funct_1(A_746)) | ~v1_funct_1(B_747) | ~v1_relat_1(B_747) | ~v1_funct_1(k2_funct_1(A_746)) | ~v1_relat_1(k2_funct_1(A_746)) | ~v2_funct_1(A_746) | ~v1_funct_1(A_746) | ~v1_relat_1(A_746))), inference(superposition, [status(thm), theory('equality')], [c_26, c_760])).
% 57.63/46.93  tff(c_17835, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2935, c_17833])).
% 57.63/46.93  tff(c_17839, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_80, c_2854, c_154, c_80, c_2042, c_5459, c_17835])).
% 57.63/46.93  tff(c_27000, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19149, c_26453, c_19148, c_17839])).
% 57.63/46.93  tff(c_27001, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_27000])).
% 57.63/46.93  tff(c_77616, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77282, c_27001])).
% 57.63/46.93  tff(c_77626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_77616])).
% 57.63/46.93  tff(c_77628, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_27000])).
% 57.63/46.93  tff(c_77627, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_27000])).
% 57.63/46.93  tff(c_764, plain, (![A_14, B_144]: (k2_funct_1(k2_funct_1(A_14))=B_144 | k5_relat_1(B_144, k2_funct_1(A_14))!=k6_partfun1(k1_relat_1(A_14)) | k2_relat_1(B_144)!=k1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_26, c_760])).
% 57.63/46.93  tff(c_77664, plain, (![B_144]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))=B_144 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_144, '#skF_4') | k2_relat_1(B_144)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_77627, c_764])).
% 57.63/46.93  tff(c_78233, plain, (![B_1571]: (k2_funct_1('#skF_4')=B_1571 | k5_relat_1(B_1571, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1571)!='#skF_2' | ~v1_funct_1(B_1571) | ~v1_relat_1(B_1571))), inference(demodulation, [status(thm), theory('equality')], [c_19149, c_26453, c_77628, c_154, c_77627, c_80, c_77627, c_2854, c_77627, c_5459, c_77627, c_19148, c_77627, c_77664])).
% 57.63/46.93  tff(c_78485, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_157, c_78233])).
% 57.63/46.93  tff(c_78704, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_201, c_2183, c_78485])).
% 57.63/46.93  tff(c_78715, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78704, c_77627])).
% 57.63/46.93  tff(c_78726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_78715])).
% 57.63/46.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.63/46.93  
% 57.63/46.93  Inference rules
% 57.63/46.93  ----------------------
% 57.63/46.93  #Ref     : 0
% 57.63/46.93  #Sup     : 15759
% 57.63/46.93  #Fact    : 0
% 57.63/46.93  #Define  : 0
% 57.63/46.93  #Split   : 138
% 57.63/46.93  #Chain   : 0
% 57.63/46.93  #Close   : 0
% 57.63/46.93  
% 57.63/46.93  Ordering : KBO
% 57.63/46.93  
% 57.63/46.93  Simplification rules
% 57.63/46.93  ----------------------
% 57.63/46.93  #Subsume      : 740
% 57.63/46.93  #Demod        : 40350
% 57.63/46.93  #Tautology    : 3563
% 57.63/46.93  #SimpNegUnit  : 1080
% 57.63/46.93  #BackRed      : 167
% 57.63/46.93  
% 57.63/46.93  #Partial instantiations: 0
% 57.63/46.93  #Strategies tried      : 1
% 57.63/46.93  
% 57.63/46.93  Timing (in seconds)
% 57.63/46.93  ----------------------
% 57.69/46.93  Preprocessing        : 0.40
% 57.69/46.93  Parsing              : 0.22
% 57.69/46.93  CNF conversion       : 0.03
% 57.69/46.93  Main loop            : 45.73
% 57.69/46.93  Inferencing          : 5.87
% 57.69/46.93  Reduction            : 29.58
% 57.69/46.93  Demodulation         : 26.98
% 57.69/46.93  BG Simplification    : 0.37
% 57.69/46.93  Subsumption          : 8.70
% 57.69/46.93  Abstraction          : 0.71
% 57.69/46.93  MUC search           : 0.00
% 57.69/46.93  Cooper               : 0.00
% 57.69/46.93  Total                : 46.21
% 57.69/46.93  Index Insertion      : 0.00
% 57.69/46.93  Index Deletion       : 0.00
% 57.69/46.93  Index Matching       : 0.00
% 57.69/46.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
