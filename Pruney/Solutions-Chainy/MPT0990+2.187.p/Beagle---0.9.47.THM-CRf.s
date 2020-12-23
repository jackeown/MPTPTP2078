%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:24 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  259 (240788 expanded)
%              Number of leaves         :   44 (85007 expanded)
%              Depth                    :   37
%              Number of atoms          :  713 (933215 expanded)
%              Number of equality atoms :  227 (315855 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_233,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_114,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_100,axiom,(
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

tff(f_197,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_155,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_181,axiom,(
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

tff(f_207,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_221,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_227,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_221])).

tff(c_234,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_227])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1006,plain,(
    ! [F_134,A_132,C_133,D_131,E_136,B_135] :
      ( m1_subset_1(k1_partfun1(A_132,B_135,C_133,D_131,E_136,F_134),k1_zfmisc_1(k2_zfmisc_1(A_132,D_131)))
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(C_133,D_131)))
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_132,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_87,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_426,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_438,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_426])).

tff(c_459,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_438])).

tff(c_541,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_1026,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1006,c_541])).

tff(c_1054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1026])).

tff(c_1055,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_3252,plain,(
    ! [A_278,D_275,B_276,F_279,C_280,E_277] :
      ( k1_partfun1(A_278,B_276,C_280,D_275,E_277,F_279) = k5_relat_1(E_277,F_279)
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(C_280,D_275)))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_276)))
      | ~ v1_funct_1(E_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3264,plain,(
    ! [A_278,B_276,E_277] :
      ( k1_partfun1(A_278,B_276,'#skF_2','#skF_1',E_277,'#skF_4') = k5_relat_1(E_277,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_276)))
      | ~ v1_funct_1(E_277) ) ),
    inference(resolution,[status(thm)],[c_76,c_3252])).

tff(c_3813,plain,(
    ! [A_300,B_301,E_302] :
      ( k1_partfun1(A_300,B_301,'#skF_2','#skF_1',E_302,'#skF_4') = k5_relat_1(E_302,'#skF_4')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301)))
      | ~ v1_funct_1(E_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3264])).

tff(c_3825,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3813])).

tff(c_3834,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1055,c_3825])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_128])).

tff(c_143,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_134])).

tff(c_137,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_128])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2249,plain,(
    ! [E_216,F_214,B_215,C_213,D_211,A_212] :
      ( v1_funct_1(k1_partfun1(A_212,B_215,C_213,D_211,E_216,F_214))
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_213,D_211)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_212,B_215)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2261,plain,(
    ! [A_212,B_215,E_216] :
      ( v1_funct_1(k1_partfun1(A_212,B_215,'#skF_2','#skF_1',E_216,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_212,B_215)))
      | ~ v1_funct_1(E_216) ) ),
    inference(resolution,[status(thm)],[c_76,c_2249])).

tff(c_2371,plain,(
    ! [A_228,B_229,E_230] :
      ( v1_funct_1(k1_partfun1(A_228,B_229,'#skF_2','#skF_1',E_230,'#skF_4'))
      | ~ m1_subset_1(E_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(E_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2261])).

tff(c_2386,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2371])).

tff(c_2400,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1055,c_2386])).

tff(c_131,plain,(
    ! [A_24] :
      ( v1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(k2_zfmisc_1(A_24,A_24)) ) ),
    inference(resolution,[status(thm)],[c_87,c_128])).

tff(c_140,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_7)),A_7) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_148,plain,(
    ! [A_65] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_65)),A_65) = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_157,plain,(
    ! [A_6] :
      ( k5_relat_1(k6_partfun1(A_6),k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ v1_relat_1(k6_partfun1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_148])).

tff(c_161,plain,(
    ! [A_6] : k5_relat_1(k6_partfun1(A_6),k6_partfun1(A_6)) = k6_partfun1(A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_157])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( v2_funct_1(A_9)
      | k6_relat_1(k1_relat_1(A_9)) != k5_relat_1(A_9,B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_408,plain,(
    ! [A_84,B_85] :
      ( v2_funct_1(A_84)
      | k6_partfun1(k1_relat_1(A_84)) != k5_relat_1(A_84,B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_414,plain,(
    ! [A_6] :
      ( v2_funct_1(k6_partfun1(A_6))
      | k6_partfun1(k1_relat_1(k6_partfun1(A_6))) != k6_partfun1(A_6)
      | ~ v1_funct_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_6))
      | ~ v1_funct_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_408])).

tff(c_420,plain,(
    ! [A_6] :
      ( v2_funct_1(k6_partfun1(A_6))
      | ~ v1_funct_1(k6_partfun1(A_6)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_92,c_414])).

tff(c_1101,plain,(
    ! [B_144,A_141,E_145,F_143,C_142,D_140] :
      ( v1_funct_1(k1_partfun1(A_141,B_144,C_142,D_140,E_145,F_143))
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_142,D_140)))
      | ~ v1_funct_1(F_143)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_141,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1111,plain,(
    ! [A_141,B_144,E_145] :
      ( v1_funct_1(k1_partfun1(A_141,B_144,'#skF_2','#skF_1',E_145,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_141,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(resolution,[status(thm)],[c_76,c_1101])).

tff(c_1150,plain,(
    ! [A_149,B_150,E_151] :
      ( v1_funct_1(k1_partfun1(A_149,B_150,'#skF_2','#skF_1',E_151,'#skF_4'))
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1111])).

tff(c_1162,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1150])).

tff(c_1173,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1055,c_1162])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_26,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_relat_1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_499,plain,(
    ! [A_92,B_93] :
      ( k2_funct_1(A_92) = B_93
      | k6_partfun1(k2_relat_1(A_92)) != k5_relat_1(B_93,A_92)
      | k2_relat_1(B_93) != k1_relat_1(A_92)
      | ~ v2_funct_1(A_92)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_26])).

tff(c_505,plain,(
    ! [B_93] :
      ( k2_funct_1('#skF_3') = B_93
      | k5_relat_1(B_93,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_93) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_499])).

tff(c_1065,plain,(
    ! [B_138] :
      ( k2_funct_1('#skF_3') = B_138
      | k5_relat_1(B_138,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_138) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_86,c_70,c_505])).

tff(c_1071,plain,(
    ! [A_24] :
      ( k6_partfun1(A_24) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_24),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_24)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_140,c_1065])).

tff(c_1087,plain,(
    ! [A_24] :
      ( k6_partfun1(A_24) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_24),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_24
      | ~ v1_funct_1(k6_partfun1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1071])).

tff(c_1183,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1173,c_1087])).

tff(c_1248,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1183])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1286,plain,(
    ! [A_163,C_164,B_165] :
      ( k6_partfun1(A_163) = k5_relat_1(C_164,k2_funct_1(C_164))
      | k1_xboole_0 = B_165
      | ~ v2_funct_1(C_164)
      | k2_relset_1(A_163,B_165,C_164) != B_165
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_165)))
      | ~ v1_funct_2(C_164,A_163,B_165)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1294,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1286])).

tff(c_1307,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_1294])).

tff(c_1308,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1307])).

tff(c_24,plain,(
    ! [A_13] :
      ( k1_relat_1(k5_relat_1(A_13,k2_funct_1(A_13))) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1318,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_24])).

tff(c_1327,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_86,c_70,c_92,c_1318])).

tff(c_1329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1248,c_1327])).

tff(c_1331,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_1074,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_1065])).

tff(c_1090,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1074])).

tff(c_1091,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1090])).

tff(c_1097,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1091])).

tff(c_1336,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_1097])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_210,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_relset_1(A_71,B_72,D_73,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_217,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_87,c_210])).

tff(c_235,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_221])).

tff(c_2171,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k2_relset_1(A_207,B_208,C_209) = B_208
      | ~ r2_relset_1(B_208,B_208,k1_partfun1(B_208,A_207,A_207,B_208,D_210,C_209),k6_partfun1(B_208))
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(B_208,A_207)))
      | ~ v1_funct_2(D_210,B_208,A_207)
      | ~ v1_funct_1(D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_209,A_207,B_208)
      | ~ v1_funct_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2177,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_2171])).

tff(c_2181,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_217,c_235,c_2177])).

tff(c_2183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1336,c_2181])).

tff(c_2185,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_183,plain,(
    ! [A_69] :
      ( k1_relat_1(k2_funct_1(A_69)) = k2_relat_1(A_69)
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_90,plain,(
    ! [A_7] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_7)),A_7) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_192,plain,(
    ! [A_69] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_69)),k2_funct_1(A_69)) = k2_funct_1(A_69)
      | ~ v1_relat_1(k2_funct_1(A_69))
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_90])).

tff(c_2192,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2185,c_192])).

tff(c_2210,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_2192])).

tff(c_2276,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2210])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_3140,plain,(
    ! [A_267,E_264,D_266,C_265,B_268] :
      ( k1_xboole_0 = C_265
      | v2_funct_1(E_264)
      | k2_relset_1(A_267,B_268,D_266) != B_268
      | ~ v2_funct_1(k1_partfun1(A_267,B_268,B_268,C_265,D_266,E_264))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(B_268,C_265)))
      | ~ v1_funct_2(E_264,B_268,C_265)
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ v1_funct_2(D_266,A_267,B_268)
      | ~ v1_funct_1(D_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3144,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_3140])).

tff(c_3149,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_3144])).

tff(c_3150,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_2276,c_68,c_3149])).

tff(c_3153,plain,(
    ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_420,c_3150])).

tff(c_3157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_3153])).

tff(c_3158,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_4'))
    | k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2210])).

tff(c_3160,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3158])).

tff(c_3196,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_3160])).

tff(c_3200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3196])).

tff(c_3202,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3158])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3279,plain,(
    ! [A_281,B_282,E_283] :
      ( v1_funct_1(k1_partfun1(A_281,B_282,'#skF_2','#skF_1',E_283,'#skF_4'))
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(E_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2261])).

tff(c_3294,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3279])).

tff(c_3308,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1055,c_3294])).

tff(c_3159,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2210])).

tff(c_3355,plain,(
    ! [A_284,C_285,B_286] :
      ( k6_partfun1(A_284) = k5_relat_1(C_285,k2_funct_1(C_285))
      | k1_xboole_0 = B_286
      | ~ v2_funct_1(C_285)
      | k2_relset_1(A_284,B_286,C_285) != B_286
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_284,B_286)))
      | ~ v1_funct_2(C_285,A_284,B_286)
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3365,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3355])).

tff(c_3381,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_3365])).

tff(c_3382,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3381])).

tff(c_3392,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3382,c_24])).

tff(c_3401,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_86,c_70,c_92,c_3392])).

tff(c_3416,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_2185])).

tff(c_3468,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_192])).

tff(c_3486,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3202,c_3468])).

tff(c_89,plain,(
    ! [A_9,B_11] :
      ( v2_funct_1(A_9)
      | k6_partfun1(k1_relat_1(A_9)) != k5_relat_1(A_9,B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_3652,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | k6_partfun1(k1_relat_1(k6_partfun1('#skF_1'))) != k2_funct_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3486,c_89])).

tff(c_3658,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_3308,c_3202,c_92,c_3652])).

tff(c_3929,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3658])).

tff(c_3934,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3929])).

tff(c_3938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3934])).

tff(c_3940,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3658])).

tff(c_60,plain,(
    ! [A_52] :
      ( v1_funct_2(A_52,k1_relat_1(A_52),k2_relat_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_2204,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2185,c_60])).

tff(c_2218,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_2204])).

tff(c_3414,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_2218])).

tff(c_236,plain,(
    ! [A_78] :
      ( m1_subset_1(A_78,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_78),k2_relat_1(A_78))))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_257,plain,(
    ! [A_78] :
      ( k2_relset_1(k1_relat_1(A_78),k2_relat_1(A_78),A_78) = k2_relat_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_236,c_28])).

tff(c_2195,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'),'#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2185,c_257])).

tff(c_2212,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'),'#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_2185,c_2195])).

tff(c_3411,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_3401,c_2212])).

tff(c_58,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52))))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_2201,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2185,c_58])).

tff(c_2216,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_2201])).

tff(c_3412,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_2216])).

tff(c_56,plain,(
    ! [A_49,C_51,B_50] :
      ( k6_partfun1(A_49) = k5_relat_1(C_51,k2_funct_1(C_51))
      | k1_xboole_0 = B_50
      | ~ v2_funct_1(C_51)
      | k2_relset_1(A_49,B_50,C_51) != B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3561,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3412,c_56])).

tff(c_3586,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3414,c_3411,c_3159,c_3561])).

tff(c_3587,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3586])).

tff(c_2186,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_235])).

tff(c_3367,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3355])).

tff(c_3385,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2186,c_3159,c_3367])).

tff(c_3386,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3385])).

tff(c_3681,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_3587,c_3386])).

tff(c_3720,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3681,c_91])).

tff(c_3738,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3720])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6202,plain,(
    ! [A_370] :
      ( v1_funct_2(k2_funct_1(A_370),k2_relat_1(A_370),k2_relat_1(k2_funct_1(A_370)))
      | ~ v1_funct_1(k2_funct_1(A_370))
      | ~ v1_relat_1(k2_funct_1(A_370))
      | ~ v2_funct_1(A_370)
      | ~ v1_funct_1(A_370)
      | ~ v1_relat_1(A_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_60])).

tff(c_6211,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_6202])).

tff(c_6238,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3202,c_3940,c_6211])).

tff(c_6249,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6238])).

tff(c_6251,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3738,c_6249])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6679,plain,(
    ! [A_375] :
      ( m1_subset_1(k2_funct_1(A_375),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_375),k2_relat_1(k2_funct_1(A_375)))))
      | ~ v1_funct_1(k2_funct_1(A_375))
      | ~ v1_relat_1(k2_funct_1(A_375))
      | ~ v2_funct_1(A_375)
      | ~ v1_funct_1(A_375)
      | ~ v1_relat_1(A_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_236])).

tff(c_6718,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_6679])).

tff(c_6759,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3202,c_3940,c_6718])).

tff(c_7599,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6759])).

tff(c_7633,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3738,c_7599])).

tff(c_509,plain,(
    ! [A_6] :
      ( k2_funct_1(k6_partfun1(A_6)) = k6_partfun1(A_6)
      | k6_partfun1(k2_relat_1(k6_partfun1(A_6))) != k6_partfun1(A_6)
      | k2_relat_1(k6_partfun1(A_6)) != k1_relat_1(k6_partfun1(A_6))
      | ~ v2_funct_1(k6_partfun1(A_6))
      | ~ v1_funct_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_6))
      | ~ v1_funct_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_499])).

tff(c_536,plain,(
    ! [A_94] :
      ( k2_funct_1(k6_partfun1(A_94)) = k6_partfun1(A_94)
      | ~ v2_funct_1(k6_partfun1(A_94))
      | ~ v1_funct_1(k6_partfun1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_92,c_91,c_91,c_509])).

tff(c_540,plain,(
    ! [A_6] :
      ( k2_funct_1(k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ v1_funct_1(k6_partfun1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_420,c_536])).

tff(c_3315,plain,(
    k2_funct_1(k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3308,c_540])).

tff(c_6214,plain,
    ( v1_funct_2(k6_partfun1('#skF_1'),k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1(k2_funct_1(k6_partfun1('#skF_1'))))
    | ~ v1_funct_1(k2_funct_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1(k6_partfun1('#skF_1')))
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3315,c_6202])).

tff(c_6240,plain,
    ( v1_funct_2(k6_partfun1('#skF_1'),'#skF_1','#skF_1')
    | ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_3308,c_140,c_3315,c_3308,c_3315,c_91,c_91,c_3315,c_6214])).

tff(c_6252,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6240])).

tff(c_6257,plain,(
    ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_420,c_6252])).

tff(c_6261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3308,c_6257])).

tff(c_6263,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6240])).

tff(c_7693,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7633,c_28])).

tff(c_3415,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_2186])).

tff(c_3508,plain,(
    ! [B_287,C_288,A_289] :
      ( k6_partfun1(B_287) = k5_relat_1(k2_funct_1(C_288),C_288)
      | k1_xboole_0 = B_287
      | ~ v2_funct_1(C_288)
      | k2_relset_1(A_289,B_287,C_288) != B_287
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_289,B_287)))
      | ~ v1_funct_2(C_288,A_289,B_287)
      | ~ v1_funct_1(C_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3516,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3508])).

tff(c_3527,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3415,c_3159,c_3516])).

tff(c_3528,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3527])).

tff(c_3278,plain,(
    ! [A_278,B_276,E_277] :
      ( k1_partfun1(A_278,B_276,'#skF_2','#skF_1',E_277,'#skF_4') = k5_relat_1(E_277,'#skF_4')
      | ~ m1_subset_1(E_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_276)))
      | ~ v1_funct_1(E_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3264])).

tff(c_7641,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7633,c_3278])).

tff(c_7672,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1',k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3940,c_3528,c_7641])).

tff(c_52,plain,(
    ! [E_48,D_46,C_45,A_43,B_44] :
      ( k1_xboole_0 = C_45
      | v2_funct_1(D_46)
      | k2_relset_1(A_43,B_44,D_46) != B_44
      | ~ v2_funct_1(k1_partfun1(A_43,B_44,B_44,C_45,D_46,E_48))
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(B_44,C_45)))
      | ~ v1_funct_2(E_48,B_44,C_45)
      | ~ v1_funct_1(E_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(D_46,A_43,B_44)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_7875,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7672,c_52])).

tff(c_7887,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3940,c_6251,c_7633,c_80,c_78,c_76,c_6263,c_7693,c_7875])).

tff(c_7888,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7887])).

tff(c_7960,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7888])).

tff(c_7963,plain,
    ( k1_relat_1('#skF_4') != '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_7960])).

tff(c_7966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3738,c_7963])).

tff(c_7967,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7888])).

tff(c_7968,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7888])).

tff(c_7645,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7633,c_56])).

tff(c_7679,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3940,c_6251,c_7645])).

tff(c_7680,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7679])).

tff(c_7970,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7693,c_7967,c_7680])).

tff(c_7971,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7970])).

tff(c_8059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7968,c_7971])).

tff(c_8060,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7970])).

tff(c_8176,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8060,c_24])).

tff(c_8189,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3202,c_3940,c_7967,c_92,c_8176])).

tff(c_3682,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3681,c_3587])).

tff(c_10131,plain,(
    ! [A_432,B_433] :
      ( k2_funct_1(k2_funct_1(A_432)) = B_433
      | k5_relat_1(B_433,k2_funct_1(A_432)) != k6_partfun1(k1_relat_1(A_432))
      | k2_relat_1(B_433) != k1_relat_1(k2_funct_1(A_432))
      | ~ v2_funct_1(k2_funct_1(A_432))
      | ~ v1_funct_1(B_433)
      | ~ v1_relat_1(B_433)
      | ~ v1_funct_1(k2_funct_1(A_432))
      | ~ v1_relat_1(k2_funct_1(A_432))
      | ~ v2_funct_1(A_432)
      | ~ v1_funct_1(A_432)
      | ~ v1_relat_1(A_432) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_499])).

tff(c_10145,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_3682,c_10131])).

tff(c_10174,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3159,c_3202,c_3940,c_146,c_80,c_7967,c_3416,c_8189,c_3738,c_10145])).

tff(c_507,plain,(
    ! [A_12,B_93] :
      ( k2_funct_1(k2_funct_1(A_12)) = B_93
      | k5_relat_1(B_93,k2_funct_1(A_12)) != k6_partfun1(k1_relat_1(A_12))
      | k2_relat_1(B_93) != k1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_499])).

tff(c_10347,plain,(
    ! [B_93] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) = B_93
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_93,'#skF_4')
      | k2_relat_1(B_93) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10174,c_507])).

tff(c_16359,plain,(
    ! [B_547] :
      ( k2_funct_1('#skF_4') = B_547
      | k5_relat_1(B_547,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_547) != '#skF_2'
      | ~ v1_funct_1(B_547)
      | ~ v1_relat_1(B_547) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3202,c_3940,c_7967,c_146,c_10174,c_80,c_10174,c_3159,c_10174,c_3738,c_10174,c_8189,c_10174,c_10347])).

tff(c_16602,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_143,c_16359])).

tff(c_16803,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_234,c_3834,c_16602])).

tff(c_16828,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16803,c_10174])).

tff(c_16872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_16828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.92/5.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/5.25  
% 11.92/5.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.09/5.25  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.09/5.25  
% 12.09/5.25  %Foreground sorts:
% 12.09/5.25  
% 12.09/5.25  
% 12.09/5.25  %Background operators:
% 12.09/5.25  
% 12.09/5.25  
% 12.09/5.25  %Foreground operators:
% 12.09/5.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.09/5.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.09/5.25  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.09/5.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.09/5.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.09/5.25  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.09/5.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.09/5.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.09/5.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.09/5.25  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.09/5.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.09/5.25  tff('#skF_2', type, '#skF_2': $i).
% 12.09/5.25  tff('#skF_3', type, '#skF_3': $i).
% 12.09/5.25  tff('#skF_1', type, '#skF_1': $i).
% 12.09/5.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.09/5.25  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.09/5.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.09/5.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.09/5.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.09/5.25  tff('#skF_4', type, '#skF_4': $i).
% 12.09/5.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.09/5.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.09/5.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.09/5.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.09/5.25  
% 12.09/5.32  tff(f_233, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 12.09/5.32  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.09/5.32  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.09/5.32  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.09/5.32  tff(f_114, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 12.09/5.32  tff(f_112, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.09/5.32  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.09/5.32  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.09/5.32  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.09/5.32  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.09/5.32  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.09/5.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 12.09/5.32  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 12.09/5.32  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 12.09/5.32  tff(f_197, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 12.09/5.32  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 12.09/5.32  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 12.09/5.32  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.09/5.32  tff(f_181, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 12.09/5.32  tff(f_207, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.09/5.32  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_221, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.09/5.32  tff(c_227, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_221])).
% 12.09/5.32  tff(c_234, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_227])).
% 12.09/5.32  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_1006, plain, (![F_134, A_132, C_133, D_131, E_136, B_135]: (m1_subset_1(k1_partfun1(A_132, B_135, C_133, D_131, E_136, F_134), k1_zfmisc_1(k2_zfmisc_1(A_132, D_131))) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(C_133, D_131))) | ~v1_funct_1(F_134) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_132, B_135))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.09/5.32  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.09/5.32  tff(c_34, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.09/5.32  tff(c_87, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 12.09/5.32  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_426, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.09/5.32  tff(c_438, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_426])).
% 12.09/5.32  tff(c_459, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_438])).
% 12.09/5.32  tff(c_541, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_459])).
% 12.09/5.32  tff(c_1026, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1006, c_541])).
% 12.09/5.32  tff(c_1054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1026])).
% 12.09/5.32  tff(c_1055, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_459])).
% 12.09/5.32  tff(c_3252, plain, (![A_278, D_275, B_276, F_279, C_280, E_277]: (k1_partfun1(A_278, B_276, C_280, D_275, E_277, F_279)=k5_relat_1(E_277, F_279) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(C_280, D_275))) | ~v1_funct_1(F_279) | ~m1_subset_1(E_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_276))) | ~v1_funct_1(E_277))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.09/5.32  tff(c_3264, plain, (![A_278, B_276, E_277]: (k1_partfun1(A_278, B_276, '#skF_2', '#skF_1', E_277, '#skF_4')=k5_relat_1(E_277, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_276))) | ~v1_funct_1(E_277))), inference(resolution, [status(thm)], [c_76, c_3252])).
% 12.09/5.32  tff(c_3813, plain, (![A_300, B_301, E_302]: (k1_partfun1(A_300, B_301, '#skF_2', '#skF_1', E_302, '#skF_4')=k5_relat_1(E_302, '#skF_4') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))) | ~v1_funct_1(E_302))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3264])).
% 12.09/5.32  tff(c_3825, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3813])).
% 12.09/5.32  tff(c_3834, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1055, c_3825])).
% 12.09/5.32  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.09/5.32  tff(c_128, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.09/5.32  tff(c_134, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_128])).
% 12.09/5.32  tff(c_143, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_134])).
% 12.09/5.32  tff(c_137, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_128])).
% 12.09/5.32  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_137])).
% 12.09/5.32  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.09/5.32  tff(c_2249, plain, (![E_216, F_214, B_215, C_213, D_211, A_212]: (v1_funct_1(k1_partfun1(A_212, B_215, C_213, D_211, E_216, F_214)) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_213, D_211))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_212, B_215))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.09/5.32  tff(c_2261, plain, (![A_212, B_215, E_216]: (v1_funct_1(k1_partfun1(A_212, B_215, '#skF_2', '#skF_1', E_216, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_212, B_215))) | ~v1_funct_1(E_216))), inference(resolution, [status(thm)], [c_76, c_2249])).
% 12.09/5.32  tff(c_2371, plain, (![A_228, B_229, E_230]: (v1_funct_1(k1_partfun1(A_228, B_229, '#skF_2', '#skF_1', E_230, '#skF_4')) | ~m1_subset_1(E_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(E_230))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2261])).
% 12.09/5.32  tff(c_2386, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2371])).
% 12.09/5.32  tff(c_2400, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1055, c_2386])).
% 12.09/5.32  tff(c_131, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(k2_zfmisc_1(A_24, A_24)))), inference(resolution, [status(thm)], [c_87, c_128])).
% 12.09/5.32  tff(c_140, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_131])).
% 12.09/5.32  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.09/5.32  tff(c_92, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 12.09/5.32  tff(c_10, plain, (![A_7]: (k5_relat_1(k6_relat_1(k1_relat_1(A_7)), A_7)=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.09/5.32  tff(c_148, plain, (![A_65]: (k5_relat_1(k6_partfun1(k1_relat_1(A_65)), A_65)=A_65 | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 12.09/5.32  tff(c_157, plain, (![A_6]: (k5_relat_1(k6_partfun1(A_6), k6_partfun1(A_6))=k6_partfun1(A_6) | ~v1_relat_1(k6_partfun1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_148])).
% 12.09/5.32  tff(c_161, plain, (![A_6]: (k5_relat_1(k6_partfun1(A_6), k6_partfun1(A_6))=k6_partfun1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_157])).
% 12.09/5.32  tff(c_16, plain, (![A_9, B_11]: (v2_funct_1(A_9) | k6_relat_1(k1_relat_1(A_9))!=k5_relat_1(A_9, B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.09/5.32  tff(c_408, plain, (![A_84, B_85]: (v2_funct_1(A_84) | k6_partfun1(k1_relat_1(A_84))!=k5_relat_1(A_84, B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 12.09/5.32  tff(c_414, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)) | k6_partfun1(k1_relat_1(k6_partfun1(A_6)))!=k6_partfun1(A_6) | ~v1_funct_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_6)) | ~v1_funct_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_408])).
% 12.09/5.32  tff(c_420, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)) | ~v1_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_92, c_414])).
% 12.09/5.32  tff(c_1101, plain, (![B_144, A_141, E_145, F_143, C_142, D_140]: (v1_funct_1(k1_partfun1(A_141, B_144, C_142, D_140, E_145, F_143)) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_142, D_140))) | ~v1_funct_1(F_143) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_141, B_144))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.09/5.32  tff(c_1111, plain, (![A_141, B_144, E_145]: (v1_funct_1(k1_partfun1(A_141, B_144, '#skF_2', '#skF_1', E_145, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_141, B_144))) | ~v1_funct_1(E_145))), inference(resolution, [status(thm)], [c_76, c_1101])).
% 12.09/5.32  tff(c_1150, plain, (![A_149, B_150, E_151]: (v1_funct_1(k1_partfun1(A_149, B_150, '#skF_2', '#skF_1', E_151, '#skF_4')) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(E_151))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1111])).
% 12.09/5.32  tff(c_1162, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1150])).
% 12.09/5.32  tff(c_1173, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1055, c_1162])).
% 12.09/5.32  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.09/5.32  tff(c_91, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 12.09/5.32  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_26, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_relat_1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.09/5.32  tff(c_499, plain, (![A_92, B_93]: (k2_funct_1(A_92)=B_93 | k6_partfun1(k2_relat_1(A_92))!=k5_relat_1(B_93, A_92) | k2_relat_1(B_93)!=k1_relat_1(A_92) | ~v2_funct_1(A_92) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_26])).
% 12.09/5.32  tff(c_505, plain, (![B_93]: (k2_funct_1('#skF_3')=B_93 | k5_relat_1(B_93, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_93)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_499])).
% 12.09/5.32  tff(c_1065, plain, (![B_138]: (k2_funct_1('#skF_3')=B_138 | k5_relat_1(B_138, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_138)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_86, c_70, c_505])).
% 12.09/5.32  tff(c_1071, plain, (![A_24]: (k6_partfun1(A_24)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_24), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_24))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_140, c_1065])).
% 12.09/5.32  tff(c_1087, plain, (![A_24]: (k6_partfun1(A_24)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_24), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_24 | ~v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1071])).
% 12.09/5.32  tff(c_1183, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_1173, c_1087])).
% 12.09/5.32  tff(c_1248, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1183])).
% 12.09/5.32  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_1286, plain, (![A_163, C_164, B_165]: (k6_partfun1(A_163)=k5_relat_1(C_164, k2_funct_1(C_164)) | k1_xboole_0=B_165 | ~v2_funct_1(C_164) | k2_relset_1(A_163, B_165, C_164)!=B_165 | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_165))) | ~v1_funct_2(C_164, A_163, B_165) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.09/5.32  tff(c_1294, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1286])).
% 12.09/5.32  tff(c_1307, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_1294])).
% 12.09/5.32  tff(c_1308, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_1307])).
% 12.09/5.32  tff(c_24, plain, (![A_13]: (k1_relat_1(k5_relat_1(A_13, k2_funct_1(A_13)))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.09/5.32  tff(c_1318, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1308, c_24])).
% 12.09/5.32  tff(c_1327, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_86, c_70, c_92, c_1318])).
% 12.09/5.32  tff(c_1329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1248, c_1327])).
% 12.09/5.32  tff(c_1331, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1183])).
% 12.09/5.32  tff(c_1074, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_1065])).
% 12.09/5.32  tff(c_1090, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1074])).
% 12.09/5.32  tff(c_1091, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1090])).
% 12.09/5.32  tff(c_1097, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1091])).
% 12.09/5.32  tff(c_1336, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_1097])).
% 12.09/5.32  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_210, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.09/5.32  tff(c_217, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_87, c_210])).
% 12.09/5.32  tff(c_235, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_221])).
% 12.09/5.32  tff(c_2171, plain, (![A_207, B_208, C_209, D_210]: (k2_relset_1(A_207, B_208, C_209)=B_208 | ~r2_relset_1(B_208, B_208, k1_partfun1(B_208, A_207, A_207, B_208, D_210, C_209), k6_partfun1(B_208)) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(B_208, A_207))) | ~v1_funct_2(D_210, B_208, A_207) | ~v1_funct_1(D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_209, A_207, B_208) | ~v1_funct_1(C_209))), inference(cnfTransformation, [status(thm)], [f_155])).
% 12.09/5.32  tff(c_2177, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1055, c_2171])).
% 12.09/5.32  tff(c_2181, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_217, c_235, c_2177])).
% 12.09/5.32  tff(c_2183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1336, c_2181])).
% 12.09/5.32  tff(c_2185, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1091])).
% 12.09/5.32  tff(c_183, plain, (![A_69]: (k1_relat_1(k2_funct_1(A_69))=k2_relat_1(A_69) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.09/5.32  tff(c_90, plain, (![A_7]: (k5_relat_1(k6_partfun1(k1_relat_1(A_7)), A_7)=A_7 | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 12.09/5.32  tff(c_192, plain, (![A_69]: (k5_relat_1(k6_partfun1(k2_relat_1(A_69)), k2_funct_1(A_69))=k2_funct_1(A_69) | ~v1_relat_1(k2_funct_1(A_69)) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_183, c_90])).
% 12.09/5.32  tff(c_2192, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2185, c_192])).
% 12.09/5.32  tff(c_2210, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_2192])).
% 12.09/5.32  tff(c_2276, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2210])).
% 12.09/5.32  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_233])).
% 12.09/5.32  tff(c_3140, plain, (![A_267, E_264, D_266, C_265, B_268]: (k1_xboole_0=C_265 | v2_funct_1(E_264) | k2_relset_1(A_267, B_268, D_266)!=B_268 | ~v2_funct_1(k1_partfun1(A_267, B_268, B_268, C_265, D_266, E_264)) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(B_268, C_265))) | ~v1_funct_2(E_264, B_268, C_265) | ~v1_funct_1(E_264) | ~m1_subset_1(D_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~v1_funct_2(D_266, A_267, B_268) | ~v1_funct_1(D_266))), inference(cnfTransformation, [status(thm)], [f_181])).
% 12.09/5.32  tff(c_3144, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1055, c_3140])).
% 12.09/5.32  tff(c_3149, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_3144])).
% 12.09/5.32  tff(c_3150, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_2276, c_68, c_3149])).
% 12.09/5.32  tff(c_3153, plain, (~v1_funct_1(k6_partfun1('#skF_1'))), inference(resolution, [status(thm)], [c_420, c_3150])).
% 12.09/5.32  tff(c_3157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2400, c_3153])).
% 12.09/5.32  tff(c_3158, plain, (~v1_relat_1(k2_funct_1('#skF_4')) | k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2210])).
% 12.09/5.32  tff(c_3160, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3158])).
% 12.09/5.32  tff(c_3196, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_3160])).
% 12.09/5.32  tff(c_3200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3196])).
% 12.09/5.32  tff(c_3202, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3158])).
% 12.09/5.32  tff(c_12, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.09/5.32  tff(c_3279, plain, (![A_281, B_282, E_283]: (v1_funct_1(k1_partfun1(A_281, B_282, '#skF_2', '#skF_1', E_283, '#skF_4')) | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(E_283))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2261])).
% 12.09/5.32  tff(c_3294, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3279])).
% 12.09/5.32  tff(c_3308, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1055, c_3294])).
% 12.09/5.32  tff(c_3159, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2210])).
% 12.09/5.32  tff(c_3355, plain, (![A_284, C_285, B_286]: (k6_partfun1(A_284)=k5_relat_1(C_285, k2_funct_1(C_285)) | k1_xboole_0=B_286 | ~v2_funct_1(C_285) | k2_relset_1(A_284, B_286, C_285)!=B_286 | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_284, B_286))) | ~v1_funct_2(C_285, A_284, B_286) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.09/5.32  tff(c_3365, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3355])).
% 12.09/5.32  tff(c_3381, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_3365])).
% 12.09/5.32  tff(c_3382, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_3381])).
% 12.09/5.32  tff(c_3392, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3382, c_24])).
% 12.09/5.32  tff(c_3401, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_86, c_70, c_92, c_3392])).
% 12.09/5.32  tff(c_3416, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_2185])).
% 12.09/5.32  tff(c_3468, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3416, c_192])).
% 12.09/5.32  tff(c_3486, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3202, c_3468])).
% 12.09/5.32  tff(c_89, plain, (![A_9, B_11]: (v2_funct_1(A_9) | k6_partfun1(k1_relat_1(A_9))!=k5_relat_1(A_9, B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 12.09/5.32  tff(c_3652, plain, (v2_funct_1(k6_partfun1('#skF_1')) | k6_partfun1(k1_relat_1(k6_partfun1('#skF_1')))!=k2_funct_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3486, c_89])).
% 12.09/5.32  tff(c_3658, plain, (v2_funct_1(k6_partfun1('#skF_1')) | k6_partfun1('#skF_1')!=k2_funct_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_3308, c_3202, c_92, c_3652])).
% 12.09/5.32  tff(c_3929, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3658])).
% 12.09/5.32  tff(c_3934, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3929])).
% 12.09/5.32  tff(c_3938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3934])).
% 12.09/5.32  tff(c_3940, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3658])).
% 12.09/5.32  tff(c_60, plain, (![A_52]: (v1_funct_2(A_52, k1_relat_1(A_52), k2_relat_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_207])).
% 12.09/5.32  tff(c_2204, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2185, c_60])).
% 12.09/5.32  tff(c_2218, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_2204])).
% 12.09/5.32  tff(c_3414, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_2218])).
% 12.09/5.32  tff(c_236, plain, (![A_78]: (m1_subset_1(A_78, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_78), k2_relat_1(A_78)))) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_207])).
% 12.09/5.32  tff(c_28, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.09/5.32  tff(c_257, plain, (![A_78]: (k2_relset_1(k1_relat_1(A_78), k2_relat_1(A_78), A_78)=k2_relat_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_236, c_28])).
% 12.09/5.32  tff(c_2195, plain, (k2_relset_1(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'), '#skF_4')=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2185, c_257])).
% 12.09/5.32  tff(c_2212, plain, (k2_relset_1(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'), '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_2185, c_2195])).
% 12.09/5.32  tff(c_3411, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_3401, c_2212])).
% 12.09/5.32  tff(c_58, plain, (![A_52]: (m1_subset_1(A_52, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52)))) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_207])).
% 12.09/5.32  tff(c_2201, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_relat_1('#skF_3')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2185, c_58])).
% 12.09/5.32  tff(c_2216, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_2201])).
% 12.09/5.32  tff(c_3412, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_2216])).
% 12.09/5.32  tff(c_56, plain, (![A_49, C_51, B_50]: (k6_partfun1(A_49)=k5_relat_1(C_51, k2_funct_1(C_51)) | k1_xboole_0=B_50 | ~v2_funct_1(C_51) | k2_relset_1(A_49, B_50, C_51)!=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_51, A_49, B_50) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.09/5.32  tff(c_3561, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3412, c_56])).
% 12.09/5.32  tff(c_3586, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3414, c_3411, c_3159, c_3561])).
% 12.09/5.32  tff(c_3587, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_3586])).
% 12.09/5.32  tff(c_2186, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2185, c_235])).
% 12.09/5.32  tff(c_3367, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_3355])).
% 12.09/5.32  tff(c_3385, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2186, c_3159, c_3367])).
% 12.09/5.32  tff(c_3386, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_3385])).
% 12.09/5.32  tff(c_3681, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_3587, c_3386])).
% 12.09/5.32  tff(c_3720, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3681, c_91])).
% 12.09/5.32  tff(c_3738, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3720])).
% 12.09/5.32  tff(c_18, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.09/5.32  tff(c_6202, plain, (![A_370]: (v1_funct_2(k2_funct_1(A_370), k2_relat_1(A_370), k2_relat_1(k2_funct_1(A_370))) | ~v1_funct_1(k2_funct_1(A_370)) | ~v1_relat_1(k2_funct_1(A_370)) | ~v2_funct_1(A_370) | ~v1_funct_1(A_370) | ~v1_relat_1(A_370))), inference(superposition, [status(thm), theory('equality')], [c_183, c_60])).
% 12.09/5.32  tff(c_6211, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3416, c_6202])).
% 12.09/5.32  tff(c_6238, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3202, c_3940, c_6211])).
% 12.09/5.32  tff(c_6249, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_6238])).
% 12.09/5.32  tff(c_6251, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3738, c_6249])).
% 12.09/5.32  tff(c_20, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.09/5.32  tff(c_6679, plain, (![A_375]: (m1_subset_1(k2_funct_1(A_375), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_375), k2_relat_1(k2_funct_1(A_375))))) | ~v1_funct_1(k2_funct_1(A_375)) | ~v1_relat_1(k2_funct_1(A_375)) | ~v2_funct_1(A_375) | ~v1_funct_1(A_375) | ~v1_relat_1(A_375))), inference(superposition, [status(thm), theory('equality')], [c_20, c_236])).
% 12.09/5.32  tff(c_6718, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3416, c_6679])).
% 12.09/5.32  tff(c_6759, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3202, c_3940, c_6718])).
% 12.09/5.32  tff(c_7599, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_6759])).
% 12.09/5.32  tff(c_7633, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3738, c_7599])).
% 12.09/5.32  tff(c_509, plain, (![A_6]: (k2_funct_1(k6_partfun1(A_6))=k6_partfun1(A_6) | k6_partfun1(k2_relat_1(k6_partfun1(A_6)))!=k6_partfun1(A_6) | k2_relat_1(k6_partfun1(A_6))!=k1_relat_1(k6_partfun1(A_6)) | ~v2_funct_1(k6_partfun1(A_6)) | ~v1_funct_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_6)) | ~v1_funct_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_499])).
% 12.09/5.32  tff(c_536, plain, (![A_94]: (k2_funct_1(k6_partfun1(A_94))=k6_partfun1(A_94) | ~v2_funct_1(k6_partfun1(A_94)) | ~v1_funct_1(k6_partfun1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_92, c_91, c_91, c_509])).
% 12.09/5.32  tff(c_540, plain, (![A_6]: (k2_funct_1(k6_partfun1(A_6))=k6_partfun1(A_6) | ~v1_funct_1(k6_partfun1(A_6)))), inference(resolution, [status(thm)], [c_420, c_536])).
% 12.09/5.32  tff(c_3315, plain, (k2_funct_1(k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(resolution, [status(thm)], [c_3308, c_540])).
% 12.09/5.32  tff(c_6214, plain, (v1_funct_2(k6_partfun1('#skF_1'), k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1(k2_funct_1(k6_partfun1('#skF_1')))) | ~v1_funct_1(k2_funct_1(k6_partfun1('#skF_1'))) | ~v1_relat_1(k2_funct_1(k6_partfun1('#skF_1'))) | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3315, c_6202])).
% 12.09/5.32  tff(c_6240, plain, (v1_funct_2(k6_partfun1('#skF_1'), '#skF_1', '#skF_1') | ~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_3308, c_140, c_3315, c_3308, c_3315, c_91, c_91, c_3315, c_6214])).
% 12.09/5.32  tff(c_6252, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_6240])).
% 12.09/5.32  tff(c_6257, plain, (~v1_funct_1(k6_partfun1('#skF_1'))), inference(resolution, [status(thm)], [c_420, c_6252])).
% 12.09/5.32  tff(c_6261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3308, c_6257])).
% 12.09/5.32  tff(c_6263, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_6240])).
% 12.09/5.32  tff(c_7693, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7633, c_28])).
% 12.09/5.32  tff(c_3415, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_2186])).
% 12.09/5.32  tff(c_3508, plain, (![B_287, C_288, A_289]: (k6_partfun1(B_287)=k5_relat_1(k2_funct_1(C_288), C_288) | k1_xboole_0=B_287 | ~v2_funct_1(C_288) | k2_relset_1(A_289, B_287, C_288)!=B_287 | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_289, B_287))) | ~v1_funct_2(C_288, A_289, B_287) | ~v1_funct_1(C_288))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.09/5.32  tff(c_3516, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_3508])).
% 12.09/5.32  tff(c_3527, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3415, c_3159, c_3516])).
% 12.09/5.32  tff(c_3528, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_3527])).
% 12.09/5.32  tff(c_3278, plain, (![A_278, B_276, E_277]: (k1_partfun1(A_278, B_276, '#skF_2', '#skF_1', E_277, '#skF_4')=k5_relat_1(E_277, '#skF_4') | ~m1_subset_1(E_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_276))) | ~v1_funct_1(E_277))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3264])).
% 12.09/5.32  tff(c_7641, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7633, c_3278])).
% 12.09/5.32  tff(c_7672, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3940, c_3528, c_7641])).
% 12.09/5.32  tff(c_52, plain, (![E_48, D_46, C_45, A_43, B_44]: (k1_xboole_0=C_45 | v2_funct_1(D_46) | k2_relset_1(A_43, B_44, D_46)!=B_44 | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_181])).
% 12.09/5.32  tff(c_7875, plain, (k1_xboole_0='#skF_1' | v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7672, c_52])).
% 12.09/5.32  tff(c_7887, plain, (k1_xboole_0='#skF_1' | v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3940, c_6251, c_7633, c_80, c_78, c_76, c_6263, c_7693, c_7875])).
% 12.09/5.32  tff(c_7888, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_7887])).
% 12.09/5.32  tff(c_7960, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7888])).
% 12.09/5.32  tff(c_7963, plain, (k1_relat_1('#skF_4')!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_7960])).
% 12.09/5.32  tff(c_7966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3738, c_7963])).
% 12.09/5.32  tff(c_7967, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7888])).
% 12.09/5.32  tff(c_7968, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_7888])).
% 12.09/5.32  tff(c_7645, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7633, c_56])).
% 12.09/5.32  tff(c_7679, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3940, c_6251, c_7645])).
% 12.09/5.32  tff(c_7680, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_7679])).
% 12.09/5.32  tff(c_7970, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7693, c_7967, c_7680])).
% 12.09/5.32  tff(c_7971, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7970])).
% 12.09/5.32  tff(c_8059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7968, c_7971])).
% 12.09/5.32  tff(c_8060, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_7970])).
% 12.09/5.32  tff(c_8176, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8060, c_24])).
% 12.09/5.32  tff(c_8189, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3202, c_3940, c_7967, c_92, c_8176])).
% 12.09/5.32  tff(c_3682, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3681, c_3587])).
% 12.09/5.32  tff(c_10131, plain, (![A_432, B_433]: (k2_funct_1(k2_funct_1(A_432))=B_433 | k5_relat_1(B_433, k2_funct_1(A_432))!=k6_partfun1(k1_relat_1(A_432)) | k2_relat_1(B_433)!=k1_relat_1(k2_funct_1(A_432)) | ~v2_funct_1(k2_funct_1(A_432)) | ~v1_funct_1(B_433) | ~v1_relat_1(B_433) | ~v1_funct_1(k2_funct_1(A_432)) | ~v1_relat_1(k2_funct_1(A_432)) | ~v2_funct_1(A_432) | ~v1_funct_1(A_432) | ~v1_relat_1(A_432))), inference(superposition, [status(thm), theory('equality')], [c_18, c_499])).
% 12.09/5.32  tff(c_10145, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3682, c_10131])).
% 12.09/5.32  tff(c_10174, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3159, c_3202, c_3940, c_146, c_80, c_7967, c_3416, c_8189, c_3738, c_10145])).
% 12.09/5.32  tff(c_507, plain, (![A_12, B_93]: (k2_funct_1(k2_funct_1(A_12))=B_93 | k5_relat_1(B_93, k2_funct_1(A_12))!=k6_partfun1(k1_relat_1(A_12)) | k2_relat_1(B_93)!=k1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_499])).
% 12.09/5.32  tff(c_10347, plain, (![B_93]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))=B_93 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_93, '#skF_4') | k2_relat_1(B_93)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10174, c_507])).
% 12.09/5.32  tff(c_16359, plain, (![B_547]: (k2_funct_1('#skF_4')=B_547 | k5_relat_1(B_547, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_547)!='#skF_2' | ~v1_funct_1(B_547) | ~v1_relat_1(B_547))), inference(demodulation, [status(thm), theory('equality')], [c_3202, c_3940, c_7967, c_146, c_10174, c_80, c_10174, c_3159, c_10174, c_3738, c_10174, c_8189, c_10174, c_10347])).
% 12.09/5.32  tff(c_16602, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_143, c_16359])).
% 12.09/5.32  tff(c_16803, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_234, c_3834, c_16602])).
% 12.09/5.33  tff(c_16828, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16803, c_10174])).
% 12.09/5.33  tff(c_16872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_16828])).
% 12.09/5.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.09/5.33  
% 12.09/5.33  Inference rules
% 12.09/5.33  ----------------------
% 12.09/5.33  #Ref     : 0
% 12.09/5.33  #Sup     : 3500
% 12.09/5.33  #Fact    : 0
% 12.09/5.33  #Define  : 0
% 12.09/5.33  #Split   : 69
% 12.09/5.33  #Chain   : 0
% 12.09/5.33  #Close   : 0
% 12.09/5.33  
% 12.09/5.33  Ordering : KBO
% 12.09/5.33  
% 12.09/5.33  Simplification rules
% 12.09/5.33  ----------------------
% 12.09/5.33  #Subsume      : 267
% 12.09/5.33  #Demod        : 9619
% 12.09/5.33  #Tautology    : 1322
% 12.09/5.33  #SimpNegUnit  : 324
% 12.09/5.33  #BackRed      : 184
% 12.09/5.33  
% 12.09/5.33  #Partial instantiations: 0
% 12.09/5.33  #Strategies tried      : 1
% 12.09/5.33  
% 12.09/5.33  Timing (in seconds)
% 12.09/5.33  ----------------------
% 12.09/5.33  Preprocessing        : 0.41
% 12.09/5.33  Parsing              : 0.22
% 12.09/5.33  CNF conversion       : 0.03
% 12.09/5.33  Main loop            : 4.06
% 12.09/5.33  Inferencing          : 0.96
% 12.09/5.33  Reduction            : 2.13
% 12.09/5.33  Demodulation         : 1.78
% 12.09/5.33  BG Simplification    : 0.09
% 12.09/5.33  Subsumption          : 0.67
% 12.09/5.33  Abstraction          : 0.13
% 12.09/5.33  MUC search           : 0.00
% 12.09/5.33  Cooper               : 0.00
% 12.09/5.33  Total                : 4.59
% 12.09/5.33  Index Insertion      : 0.00
% 12.09/5.33  Index Deletion       : 0.00
% 12.09/5.33  Index Matching       : 0.00
% 12.09/5.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
