%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:03 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  238 (3165 expanded)
%              Number of leaves         :   47 (1035 expanded)
%              Depth                    :   19
%              Number of atoms          :  478 (7165 expanded)
%              Number of equality atoms :  148 (2599 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_157,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_145,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_128,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_128])).

tff(c_78,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_74,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5306,plain,(
    ! [C_531,A_532,B_533] :
      ( v2_funct_1(C_531)
      | ~ v3_funct_2(C_531,A_532,B_533)
      | ~ v1_funct_1(C_531)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5312,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_5306])).

tff(c_5320,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_5312])).

tff(c_62,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5428,plain,(
    ! [A_554,B_555,C_556,D_557] :
      ( r2_relset_1(A_554,B_555,C_556,C_556)
      | ~ m1_subset_1(D_557,k1_zfmisc_1(k2_zfmisc_1(A_554,B_555)))
      | ~ m1_subset_1(C_556,k1_zfmisc_1(k2_zfmisc_1(A_554,B_555))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5438,plain,(
    ! [A_558,C_559] :
      ( r2_relset_1(A_558,A_558,C_559,C_559)
      | ~ m1_subset_1(C_559,k1_zfmisc_1(k2_zfmisc_1(A_558,A_558))) ) ),
    inference(resolution,[status(thm)],[c_62,c_5428])).

tff(c_5446,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_62,c_5438])).

tff(c_142,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_154,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_142])).

tff(c_4859,plain,(
    ! [B_482,A_483] :
      ( k2_relat_1(B_482) = A_483
      | ~ v2_funct_2(B_482,A_483)
      | ~ v5_relat_1(B_482,A_483)
      | ~ v1_relat_1(B_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4868,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_4859])).

tff(c_4877,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_4868])).

tff(c_4883,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4877])).

tff(c_5120,plain,(
    ! [C_513,B_514,A_515] :
      ( v2_funct_2(C_513,B_514)
      | ~ v3_funct_2(C_513,A_515,B_514)
      | ~ v1_funct_1(C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_515,B_514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5126,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_5120])).

tff(c_5135,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_5126])).

tff(c_5137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4883,c_5135])).

tff(c_5138,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4877])).

tff(c_68,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14])).

tff(c_76,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5544,plain,(
    ! [A_576,B_577] :
      ( k2_funct_2(A_576,B_577) = k2_funct_1(B_577)
      | ~ m1_subset_1(B_577,k1_zfmisc_1(k2_zfmisc_1(A_576,A_576)))
      | ~ v3_funct_2(B_577,A_576,A_576)
      | ~ v1_funct_2(B_577,A_576,A_576)
      | ~ v1_funct_1(B_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5550,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_5544])).

tff(c_5559,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_5550])).

tff(c_5528,plain,(
    ! [A_574,B_575] :
      ( v1_funct_1(k2_funct_2(A_574,B_575))
      | ~ m1_subset_1(B_575,k1_zfmisc_1(k2_zfmisc_1(A_574,A_574)))
      | ~ v3_funct_2(B_575,A_574,A_574)
      | ~ v1_funct_2(B_575,A_574,A_574)
      | ~ v1_funct_1(B_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5534,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_5528])).

tff(c_5542,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_5534])).

tff(c_5562,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5559,c_5542])).

tff(c_52,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_funct_2(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5809,plain,(
    ! [E_595,F_597,D_598,C_596,A_594,B_599] :
      ( k1_partfun1(A_594,B_599,C_596,D_598,E_595,F_597) = k5_relat_1(E_595,F_597)
      | ~ m1_subset_1(F_597,k1_zfmisc_1(k2_zfmisc_1(C_596,D_598)))
      | ~ v1_funct_1(F_597)
      | ~ m1_subset_1(E_595,k1_zfmisc_1(k2_zfmisc_1(A_594,B_599)))
      | ~ v1_funct_1(E_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5817,plain,(
    ! [A_594,B_599,E_595] :
      ( k1_partfun1(A_594,B_599,'#skF_1','#skF_1',E_595,'#skF_2') = k5_relat_1(E_595,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_595,k1_zfmisc_1(k2_zfmisc_1(A_594,B_599)))
      | ~ v1_funct_1(E_595) ) ),
    inference(resolution,[status(thm)],[c_72,c_5809])).

tff(c_5842,plain,(
    ! [A_600,B_601,E_602] :
      ( k1_partfun1(A_600,B_601,'#skF_1','#skF_1',E_602,'#skF_2') = k5_relat_1(E_602,'#skF_2')
      | ~ m1_subset_1(E_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601)))
      | ~ v1_funct_1(E_602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5817])).

tff(c_6114,plain,(
    ! [A_610,B_611] :
      ( k1_partfun1(A_610,A_610,'#skF_1','#skF_1',k2_funct_2(A_610,B_611),'#skF_2') = k5_relat_1(k2_funct_2(A_610,B_611),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_610,B_611))
      | ~ m1_subset_1(B_611,k1_zfmisc_1(k2_zfmisc_1(A_610,A_610)))
      | ~ v3_funct_2(B_611,A_610,A_610)
      | ~ v1_funct_2(B_611,A_610,A_610)
      | ~ v1_funct_1(B_611) ) ),
    inference(resolution,[status(thm)],[c_52,c_5842])).

tff(c_6124,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_6114])).

tff(c_6138,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_5562,c_5559,c_5559,c_5559,c_6124])).

tff(c_941,plain,(
    ! [C_128,A_129,B_130] :
      ( v2_funct_1(C_128)
      | ~ v3_funct_2(C_128,A_129,B_130)
      | ~ v1_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_947,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_941])).

tff(c_955,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_947])).

tff(c_1078,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( r2_relset_1(A_149,B_150,C_151,C_151)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1088,plain,(
    ! [A_153,C_154] :
      ( r2_relset_1(A_153,A_153,C_154,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,A_153))) ) ),
    inference(resolution,[status(thm)],[c_62,c_1078])).

tff(c_1096,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_62,c_1088])).

tff(c_10,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_174,plain,(
    ! [A_58] : v1_relat_1(k6_partfun1(A_58)) ),
    inference(resolution,[status(thm)],[c_62,c_128])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_177,plain,(
    ! [A_58] :
      ( k1_relat_1(k6_partfun1(A_58)) != k1_xboole_0
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_174,c_8])).

tff(c_182,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_177])).

tff(c_70,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_185,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_239,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_185])).

tff(c_357,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_847,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_860,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_847])).

tff(c_1038,plain,(
    ! [B_144,A_145,C_146] :
      ( k1_xboole_0 = B_144
      | k1_relset_1(A_145,B_144,C_146) = A_145
      | ~ v1_funct_2(C_146,A_145,B_144)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1044,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_1038])).

tff(c_1053,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_860,c_1044])).

tff(c_1054,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_1053])).

tff(c_16,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_80,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_1195,plain,(
    ! [A_175,B_176] :
      ( k2_funct_2(A_175,B_176) = k2_funct_1(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_zfmisc_1(A_175,A_175)))
      | ~ v3_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1201,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1195])).

tff(c_1210,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1201])).

tff(c_1164,plain,(
    ! [A_170,B_171] :
      ( v1_funct_1(k2_funct_2(A_170,B_171))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k2_zfmisc_1(A_170,A_170)))
      | ~ v3_funct_2(B_171,A_170,A_170)
      | ~ v1_funct_2(B_171,A_170,A_170)
      | ~ v1_funct_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1170,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1164])).

tff(c_1178,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1170])).

tff(c_1213,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_1178])).

tff(c_1430,plain,(
    ! [E_188,B_192,F_190,A_187,C_189,D_191] :
      ( k1_partfun1(A_187,B_192,C_189,D_191,E_188,F_190) = k5_relat_1(E_188,F_190)
      | ~ m1_subset_1(F_190,k1_zfmisc_1(k2_zfmisc_1(C_189,D_191)))
      | ~ v1_funct_1(F_190)
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_187,B_192)))
      | ~ v1_funct_1(E_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2657,plain,(
    ! [A_239,B_236,E_237,B_235,A_238] :
      ( k1_partfun1(A_238,B_235,A_239,A_239,E_237,k2_funct_2(A_239,B_236)) = k5_relat_1(E_237,k2_funct_2(A_239,B_236))
      | ~ v1_funct_1(k2_funct_2(A_239,B_236))
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_235)))
      | ~ v1_funct_1(E_237)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ v3_funct_2(B_236,A_239,A_239)
      | ~ v1_funct_2(B_236,A_239,A_239)
      | ~ v1_funct_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_52,c_1430])).

tff(c_2673,plain,(
    ! [A_239,B_236] :
      ( k1_partfun1('#skF_1','#skF_1',A_239,A_239,'#skF_2',k2_funct_2(A_239,B_236)) = k5_relat_1('#skF_2',k2_funct_2(A_239,B_236))
      | ~ v1_funct_1(k2_funct_2(A_239,B_236))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_239,A_239)))
      | ~ v3_funct_2(B_236,A_239,A_239)
      | ~ v1_funct_2(B_236,A_239,A_239)
      | ~ v1_funct_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_72,c_2657])).

tff(c_2759,plain,(
    ! [A_240,B_241] :
      ( k1_partfun1('#skF_1','#skF_1',A_240,A_240,'#skF_2',k2_funct_2(A_240,B_241)) = k5_relat_1('#skF_2',k2_funct_2(A_240,B_241))
      | ~ v1_funct_1(k2_funct_2(A_240,B_241))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(k2_zfmisc_1(A_240,A_240)))
      | ~ v3_funct_2(B_241,A_240,A_240)
      | ~ v1_funct_2(B_241,A_240,A_240)
      | ~ v1_funct_1(B_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2673])).

tff(c_2775,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_2759])).

tff(c_2798,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1213,c_1210,c_1210,c_1210,c_2775])).

tff(c_1214,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_185])).

tff(c_2822,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_1214])).

tff(c_2829,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_2822])).

tff(c_2835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_78,c_955,c_1096,c_1054,c_2829])).

tff(c_2837,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_6,plain,(
    ! [A_5] :
      ( k2_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_163,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_245,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_2846,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2837,c_245])).

tff(c_2869,plain,(
    ! [B_245,A_246] :
      ( k2_relat_1(B_245) = A_246
      | ~ v2_funct_2(B_245,A_246)
      | ~ v5_relat_1(B_245,A_246)
      | ~ v1_relat_1(B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2878,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_2869])).

tff(c_2887,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2878])).

tff(c_3027,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2846,c_2887])).

tff(c_3243,plain,(
    ! [C_279,B_280,A_281] :
      ( v2_funct_2(C_279,B_280)
      | ~ v3_funct_2(C_279,A_281,B_280)
      | ~ v1_funct_1(C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3253,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_3243])).

tff(c_3259,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_3253])).

tff(c_3261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3027,c_3259])).

tff(c_3262,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_189,plain,(
    ! [A_61] :
      ( k1_xboole_0 != A_61
      | k6_partfun1(A_61) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_177])).

tff(c_209,plain,(
    ! [A_61] :
      ( k1_relat_1(k1_xboole_0) = A_61
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_83])).

tff(c_3386,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3262,c_3262,c_209])).

tff(c_162,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_221,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_3264,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3262,c_221])).

tff(c_3389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_3264])).

tff(c_3390,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_12,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_180,plain,(
    ! [A_58] :
      ( k2_relat_1(k6_partfun1(A_58)) != k1_xboole_0
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_184,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_180])).

tff(c_3445,plain,(
    ! [A_299] :
      ( A_299 != '#skF_2'
      | k6_partfun1(A_299) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_3390,c_184])).

tff(c_3454,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3445,c_185])).

tff(c_3500,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3454])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3398,plain,(
    ! [A_1] : m1_subset_1('#skF_2',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_2])).

tff(c_3791,plain,(
    ! [C_336,B_337,A_338] :
      ( v2_funct_2(C_336,B_337)
      | ~ v3_funct_2(C_336,A_338,B_337)
      | ~ v1_funct_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3795,plain,(
    ! [B_337,A_338] :
      ( v2_funct_2('#skF_2',B_337)
      | ~ v3_funct_2('#skF_2',A_338,B_337)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3398,c_3791])).

tff(c_3804,plain,(
    ! [B_339,A_340] :
      ( v2_funct_2('#skF_2',B_339)
      | ~ v3_funct_2('#skF_2',A_340,B_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3795])).

tff(c_3808,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_3804])).

tff(c_212,plain,(
    ! [A_61] :
      ( k2_relat_1(k1_xboole_0) = A_61
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_82])).

tff(c_3493,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_3390,c_212])).

tff(c_155,plain,(
    ! [B_56] : v5_relat_1(k1_xboole_0,B_56) ),
    inference(resolution,[status(thm)],[c_2,c_142])).

tff(c_3393,plain,(
    ! [B_56] : v5_relat_1('#skF_2',B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_155])).

tff(c_3526,plain,(
    ! [B_309,A_310] :
      ( k2_relat_1(B_309) = A_310
      | ~ v2_funct_2(B_309,A_310)
      | ~ v5_relat_1(B_309,A_310)
      | ~ v1_relat_1(B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3529,plain,(
    ! [B_56] :
      ( k2_relat_1('#skF_2') = B_56
      | ~ v2_funct_2('#skF_2',B_56)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3393,c_3526])).

tff(c_3535,plain,(
    ! [B_56] :
      ( B_56 = '#skF_2'
      | ~ v2_funct_2('#skF_2',B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_3493,c_3529])).

tff(c_3811,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3808,c_3535])).

tff(c_3815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3500,c_3811])).

tff(c_3817,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3454])).

tff(c_3821,plain,(
    ! [A_1] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3398])).

tff(c_4327,plain,(
    ! [A_399,B_400,C_401,D_402] :
      ( r2_relset_1(A_399,B_400,C_401,C_401)
      | ~ m1_subset_1(D_402,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4386,plain,(
    ! [A_415,B_416,C_417] :
      ( r2_relset_1(A_415,B_416,C_417,C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(resolution,[status(thm)],[c_3821,c_4327])).

tff(c_4392,plain,(
    ! [A_415,B_416] : r2_relset_1(A_415,B_416,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3821,c_4386])).

tff(c_3829,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_78])).

tff(c_3826,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_140])).

tff(c_4065,plain,(
    ! [C_364,A_365,B_366] :
      ( v2_funct_1(C_364)
      | ~ v3_funct_2(C_364,A_365,B_366)
      | ~ v1_funct_1(C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_365,B_366))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4069,plain,(
    ! [A_365,B_366] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_365,B_366)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3821,c_4065])).

tff(c_4075,plain,(
    ! [A_365,B_366] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_365,B_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_4069])).

tff(c_4081,plain,(
    ! [A_365,B_366] : ~ v3_funct_2('#skF_1',A_365,B_366) ),
    inference(splitLeft,[status(thm)],[c_4075])).

tff(c_3827,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_74])).

tff(c_4083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4081,c_3827])).

tff(c_4084,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4075])).

tff(c_3443,plain,(
    ! [A_58] :
      ( A_58 != '#skF_2'
      | k6_partfun1(A_58) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_3390,c_184])).

tff(c_3897,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3817,c_3443])).

tff(c_3474,plain,(
    ! [A_299] :
      ( k2_relat_1('#skF_2') = A_299
      | A_299 != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3445,c_82])).

tff(c_3940,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3817,c_3474])).

tff(c_3825,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3390])).

tff(c_18,plain,(
    ! [A_8] : k2_funct_1(k6_relat_1(A_8)) = k6_relat_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    ! [A_8] : k2_funct_1(k6_partfun1(A_8)) = k6_partfun1(A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_18])).

tff(c_203,plain,(
    ! [A_61] :
      ( k6_partfun1(A_61) = k2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_79])).

tff(c_3989,plain,(
    ! [A_359] :
      ( k6_partfun1(A_359) = k2_funct_1('#skF_1')
      | A_359 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3825,c_203])).

tff(c_4059,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3989,c_83])).

tff(c_139,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_62,c_128])).

tff(c_4009,plain,(
    ! [A_359] :
      ( v1_relat_1(k2_funct_1('#skF_1'))
      | A_359 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3989,c_139])).

tff(c_4033,plain,(
    ! [A_359] : A_359 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4009])).

tff(c_3391,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_3413,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_3391])).

tff(c_3824,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3817,c_3413])).

tff(c_3952,plain,(
    ! [A_352,B_353,C_354] :
      ( k1_relset_1(A_352,B_353,C_354) = k1_relat_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_352,B_353))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3956,plain,(
    ! [A_352,B_353] : k1_relset_1(A_352,B_353,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3821,c_3952])).

tff(c_3961,plain,(
    ! [A_352,B_353] : k1_relset_1(A_352,B_353,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3956])).

tff(c_4040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4033,c_3961])).

tff(c_4041,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4009])).

tff(c_3395,plain,(
    ! [A_5] :
      ( k1_relat_1(A_5) != '#skF_2'
      | A_5 = '#skF_2'
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3390,c_3390,c_8])).

tff(c_4144,plain,(
    ! [A_376] :
      ( k1_relat_1(A_376) != '#skF_1'
      | A_376 = '#skF_1'
      | ~ v1_relat_1(A_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3817,c_3395])).

tff(c_4147,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4041,c_4144])).

tff(c_4156,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4059,c_4147])).

tff(c_4179,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4156,c_81])).

tff(c_4186,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_3829,c_4084,c_3897,c_3940,c_4179])).

tff(c_4635,plain,(
    ! [F_449,B_451,E_447,C_448,D_450,A_446] :
      ( k1_partfun1(A_446,B_451,C_448,D_450,E_447,F_449) = k5_relat_1(E_447,F_449)
      | ~ m1_subset_1(F_449,k1_zfmisc_1(k2_zfmisc_1(C_448,D_450)))
      | ~ v1_funct_1(F_449)
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(A_446,B_451)))
      | ~ v1_funct_1(E_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4640,plain,(
    ! [B_451,E_447,C_448,D_450,A_446] :
      ( k1_partfun1(A_446,B_451,C_448,D_450,E_447,'#skF_1') = k5_relat_1(E_447,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(A_446,B_451)))
      | ~ v1_funct_1(E_447) ) ),
    inference(resolution,[status(thm)],[c_3821,c_4635])).

tff(c_4657,plain,(
    ! [C_457,E_458,A_455,B_456,D_454] :
      ( k1_partfun1(A_455,B_456,C_457,D_454,E_458,'#skF_1') = k5_relat_1(E_458,'#skF_1')
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))
      | ~ v1_funct_1(E_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_4640])).

tff(c_4662,plain,(
    ! [A_455,B_456,C_457,D_454] :
      ( k1_partfun1(A_455,B_456,C_457,D_454,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3821,c_4657])).

tff(c_4668,plain,(
    ! [A_455,B_456,C_457,D_454] : k1_partfun1(A_455,B_456,C_457,D_454,'#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_4186,c_4662])).

tff(c_40,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4195,plain,(
    ! [C_377,B_378] :
      ( v1_funct_2(C_377,'#skF_1',B_378)
      | k1_relset_1('#skF_1',B_378,C_377) != '#skF_1'
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_378))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3825,c_3825,c_3825,c_40])).

tff(c_4199,plain,(
    ! [B_378] :
      ( v1_funct_2('#skF_1','#skF_1',B_378)
      | k1_relset_1('#skF_1',B_378,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3821,c_4195])).

tff(c_4206,plain,(
    ! [B_378] : v1_funct_2('#skF_1','#skF_1',B_378) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3961,c_4199])).

tff(c_4430,plain,(
    ! [A_424,B_425] :
      ( k2_funct_2(A_424,B_425) = k2_funct_1(B_425)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(k2_zfmisc_1(A_424,A_424)))
      | ~ v3_funct_2(B_425,A_424,A_424)
      | ~ v1_funct_2(B_425,A_424,A_424)
      | ~ v1_funct_1(B_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4434,plain,(
    ! [A_424] :
      ( k2_funct_2(A_424,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_424,A_424)
      | ~ v1_funct_2('#skF_1',A_424,A_424)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3821,c_4430])).

tff(c_4449,plain,(
    ! [A_427] :
      ( k2_funct_2(A_427,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_427,A_427)
      | ~ v1_funct_2('#skF_1',A_427,A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_4156,c_4434])).

tff(c_4452,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3827,c_4449])).

tff(c_4455,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4206,c_4452])).

tff(c_3822,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_3817,c_185])).

tff(c_3938,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3897,c_3822])).

tff(c_4457,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_3938])).

tff(c_4670,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4668,c_4457])).

tff(c_4673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4392,c_4670])).

tff(c_4674,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_5563,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5559,c_4674])).

tff(c_6169,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6138,c_5563])).

tff(c_6182,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_6169])).

tff(c_6188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_78,c_5320,c_5446,c_5138,c_6182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.70  
% 7.65/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.70  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.65/2.70  
% 7.65/2.70  %Foreground sorts:
% 7.65/2.70  
% 7.65/2.70  
% 7.65/2.70  %Background operators:
% 7.65/2.70  
% 7.65/2.70  
% 7.65/2.70  %Foreground operators:
% 7.65/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.65/2.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.65/2.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.65/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.65/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.65/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.65/2.70  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.65/2.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.65/2.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.65/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.65/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.65/2.70  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.70  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.65/2.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.65/2.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.65/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.65/2.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.65/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.65/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.65/2.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.65/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.65/2.70  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.65/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.65/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.65/2.70  
% 7.65/2.73  tff(f_170, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 7.65/2.73  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.65/2.73  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.65/2.73  tff(f_135, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.65/2.73  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.65/2.73  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.65/2.73  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.65/2.73  tff(f_157, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.65/2.73  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.65/2.73  tff(f_155, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.65/2.73  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.65/2.73  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.65/2.73  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.65/2.73  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.65/2.73  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.65/2.73  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.65/2.73  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.65/2.73  tff(f_57, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 7.65/2.73  tff(c_72, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.65/2.73  tff(c_128, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.65/2.73  tff(c_140, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_128])).
% 7.65/2.73  tff(c_78, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.65/2.73  tff(c_74, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.65/2.73  tff(c_5306, plain, (![C_531, A_532, B_533]: (v2_funct_1(C_531) | ~v3_funct_2(C_531, A_532, B_533) | ~v1_funct_1(C_531) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.65/2.73  tff(c_5312, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_5306])).
% 7.65/2.73  tff(c_5320, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_5312])).
% 7.65/2.73  tff(c_62, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.65/2.73  tff(c_5428, plain, (![A_554, B_555, C_556, D_557]: (r2_relset_1(A_554, B_555, C_556, C_556) | ~m1_subset_1(D_557, k1_zfmisc_1(k2_zfmisc_1(A_554, B_555))) | ~m1_subset_1(C_556, k1_zfmisc_1(k2_zfmisc_1(A_554, B_555))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.65/2.73  tff(c_5438, plain, (![A_558, C_559]: (r2_relset_1(A_558, A_558, C_559, C_559) | ~m1_subset_1(C_559, k1_zfmisc_1(k2_zfmisc_1(A_558, A_558))))), inference(resolution, [status(thm)], [c_62, c_5428])).
% 7.65/2.73  tff(c_5446, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_62, c_5438])).
% 7.65/2.73  tff(c_142, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.65/2.73  tff(c_154, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_142])).
% 7.65/2.73  tff(c_4859, plain, (![B_482, A_483]: (k2_relat_1(B_482)=A_483 | ~v2_funct_2(B_482, A_483) | ~v5_relat_1(B_482, A_483) | ~v1_relat_1(B_482))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.65/2.73  tff(c_4868, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_4859])).
% 7.65/2.73  tff(c_4877, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_4868])).
% 7.65/2.73  tff(c_4883, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4877])).
% 7.65/2.73  tff(c_5120, plain, (![C_513, B_514, A_515]: (v2_funct_2(C_513, B_514) | ~v3_funct_2(C_513, A_515, B_514) | ~v1_funct_1(C_513) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_515, B_514))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.65/2.73  tff(c_5126, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_5120])).
% 7.65/2.73  tff(c_5135, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_5126])).
% 7.65/2.73  tff(c_5137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4883, c_5135])).
% 7.65/2.73  tff(c_5138, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4877])).
% 7.65/2.73  tff(c_68, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.65/2.73  tff(c_14, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.65/2.73  tff(c_81, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14])).
% 7.65/2.73  tff(c_76, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.65/2.73  tff(c_5544, plain, (![A_576, B_577]: (k2_funct_2(A_576, B_577)=k2_funct_1(B_577) | ~m1_subset_1(B_577, k1_zfmisc_1(k2_zfmisc_1(A_576, A_576))) | ~v3_funct_2(B_577, A_576, A_576) | ~v1_funct_2(B_577, A_576, A_576) | ~v1_funct_1(B_577))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.65/2.73  tff(c_5550, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_5544])).
% 7.65/2.73  tff(c_5559, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_5550])).
% 7.65/2.73  tff(c_5528, plain, (![A_574, B_575]: (v1_funct_1(k2_funct_2(A_574, B_575)) | ~m1_subset_1(B_575, k1_zfmisc_1(k2_zfmisc_1(A_574, A_574))) | ~v3_funct_2(B_575, A_574, A_574) | ~v1_funct_2(B_575, A_574, A_574) | ~v1_funct_1(B_575))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.65/2.73  tff(c_5534, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_5528])).
% 7.65/2.73  tff(c_5542, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_5534])).
% 7.65/2.73  tff(c_5562, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5559, c_5542])).
% 7.65/2.73  tff(c_52, plain, (![A_30, B_31]: (m1_subset_1(k2_funct_2(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.65/2.73  tff(c_5809, plain, (![E_595, F_597, D_598, C_596, A_594, B_599]: (k1_partfun1(A_594, B_599, C_596, D_598, E_595, F_597)=k5_relat_1(E_595, F_597) | ~m1_subset_1(F_597, k1_zfmisc_1(k2_zfmisc_1(C_596, D_598))) | ~v1_funct_1(F_597) | ~m1_subset_1(E_595, k1_zfmisc_1(k2_zfmisc_1(A_594, B_599))) | ~v1_funct_1(E_595))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.65/2.73  tff(c_5817, plain, (![A_594, B_599, E_595]: (k1_partfun1(A_594, B_599, '#skF_1', '#skF_1', E_595, '#skF_2')=k5_relat_1(E_595, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_595, k1_zfmisc_1(k2_zfmisc_1(A_594, B_599))) | ~v1_funct_1(E_595))), inference(resolution, [status(thm)], [c_72, c_5809])).
% 7.65/2.73  tff(c_5842, plain, (![A_600, B_601, E_602]: (k1_partfun1(A_600, B_601, '#skF_1', '#skF_1', E_602, '#skF_2')=k5_relat_1(E_602, '#skF_2') | ~m1_subset_1(E_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))) | ~v1_funct_1(E_602))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5817])).
% 7.65/2.73  tff(c_6114, plain, (![A_610, B_611]: (k1_partfun1(A_610, A_610, '#skF_1', '#skF_1', k2_funct_2(A_610, B_611), '#skF_2')=k5_relat_1(k2_funct_2(A_610, B_611), '#skF_2') | ~v1_funct_1(k2_funct_2(A_610, B_611)) | ~m1_subset_1(B_611, k1_zfmisc_1(k2_zfmisc_1(A_610, A_610))) | ~v3_funct_2(B_611, A_610, A_610) | ~v1_funct_2(B_611, A_610, A_610) | ~v1_funct_1(B_611))), inference(resolution, [status(thm)], [c_52, c_5842])).
% 7.65/2.73  tff(c_6124, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_6114])).
% 7.65/2.73  tff(c_6138, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_5562, c_5559, c_5559, c_5559, c_6124])).
% 7.65/2.73  tff(c_941, plain, (![C_128, A_129, B_130]: (v2_funct_1(C_128) | ~v3_funct_2(C_128, A_129, B_130) | ~v1_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.65/2.73  tff(c_947, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_941])).
% 7.65/2.73  tff(c_955, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_947])).
% 7.65/2.73  tff(c_1078, plain, (![A_149, B_150, C_151, D_152]: (r2_relset_1(A_149, B_150, C_151, C_151) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.65/2.73  tff(c_1088, plain, (![A_153, C_154]: (r2_relset_1(A_153, A_153, C_154, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, A_153))))), inference(resolution, [status(thm)], [c_62, c_1078])).
% 7.65/2.73  tff(c_1096, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_62, c_1088])).
% 7.65/2.73  tff(c_10, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.73  tff(c_83, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10])).
% 7.65/2.73  tff(c_174, plain, (![A_58]: (v1_relat_1(k6_partfun1(A_58)))), inference(resolution, [status(thm)], [c_62, c_128])).
% 7.65/2.73  tff(c_8, plain, (![A_5]: (k1_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_177, plain, (![A_58]: (k1_relat_1(k6_partfun1(A_58))!=k1_xboole_0 | k6_partfun1(A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_174, c_8])).
% 7.65/2.73  tff(c_182, plain, (![A_58]: (k1_xboole_0!=A_58 | k6_partfun1(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_177])).
% 7.65/2.73  tff(c_70, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.65/2.73  tff(c_185, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_70])).
% 7.65/2.73  tff(c_239, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_182, c_185])).
% 7.65/2.73  tff(c_357, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_239])).
% 7.65/2.73  tff(c_847, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.65/2.73  tff(c_860, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_847])).
% 7.65/2.73  tff(c_1038, plain, (![B_144, A_145, C_146]: (k1_xboole_0=B_144 | k1_relset_1(A_145, B_144, C_146)=A_145 | ~v1_funct_2(C_146, A_145, B_144) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.65/2.73  tff(c_1044, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_1038])).
% 7.65/2.73  tff(c_1053, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_860, c_1044])).
% 7.65/2.73  tff(c_1054, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_357, c_1053])).
% 7.65/2.73  tff(c_16, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.65/2.73  tff(c_80, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16])).
% 7.65/2.73  tff(c_1195, plain, (![A_175, B_176]: (k2_funct_2(A_175, B_176)=k2_funct_1(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(k2_zfmisc_1(A_175, A_175))) | ~v3_funct_2(B_176, A_175, A_175) | ~v1_funct_2(B_176, A_175, A_175) | ~v1_funct_1(B_176))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.65/2.73  tff(c_1201, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1195])).
% 7.65/2.73  tff(c_1210, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1201])).
% 7.65/2.73  tff(c_1164, plain, (![A_170, B_171]: (v1_funct_1(k2_funct_2(A_170, B_171)) | ~m1_subset_1(B_171, k1_zfmisc_1(k2_zfmisc_1(A_170, A_170))) | ~v3_funct_2(B_171, A_170, A_170) | ~v1_funct_2(B_171, A_170, A_170) | ~v1_funct_1(B_171))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.65/2.73  tff(c_1170, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1164])).
% 7.65/2.73  tff(c_1178, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1170])).
% 7.65/2.73  tff(c_1213, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_1178])).
% 7.65/2.73  tff(c_1430, plain, (![E_188, B_192, F_190, A_187, C_189, D_191]: (k1_partfun1(A_187, B_192, C_189, D_191, E_188, F_190)=k5_relat_1(E_188, F_190) | ~m1_subset_1(F_190, k1_zfmisc_1(k2_zfmisc_1(C_189, D_191))) | ~v1_funct_1(F_190) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_187, B_192))) | ~v1_funct_1(E_188))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.65/2.73  tff(c_2657, plain, (![A_239, B_236, E_237, B_235, A_238]: (k1_partfun1(A_238, B_235, A_239, A_239, E_237, k2_funct_2(A_239, B_236))=k5_relat_1(E_237, k2_funct_2(A_239, B_236)) | ~v1_funct_1(k2_funct_2(A_239, B_236)) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_235))) | ~v1_funct_1(E_237) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_239, A_239))) | ~v3_funct_2(B_236, A_239, A_239) | ~v1_funct_2(B_236, A_239, A_239) | ~v1_funct_1(B_236))), inference(resolution, [status(thm)], [c_52, c_1430])).
% 7.65/2.73  tff(c_2673, plain, (![A_239, B_236]: (k1_partfun1('#skF_1', '#skF_1', A_239, A_239, '#skF_2', k2_funct_2(A_239, B_236))=k5_relat_1('#skF_2', k2_funct_2(A_239, B_236)) | ~v1_funct_1(k2_funct_2(A_239, B_236)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_239, A_239))) | ~v3_funct_2(B_236, A_239, A_239) | ~v1_funct_2(B_236, A_239, A_239) | ~v1_funct_1(B_236))), inference(resolution, [status(thm)], [c_72, c_2657])).
% 7.65/2.73  tff(c_2759, plain, (![A_240, B_241]: (k1_partfun1('#skF_1', '#skF_1', A_240, A_240, '#skF_2', k2_funct_2(A_240, B_241))=k5_relat_1('#skF_2', k2_funct_2(A_240, B_241)) | ~v1_funct_1(k2_funct_2(A_240, B_241)) | ~m1_subset_1(B_241, k1_zfmisc_1(k2_zfmisc_1(A_240, A_240))) | ~v3_funct_2(B_241, A_240, A_240) | ~v1_funct_2(B_241, A_240, A_240) | ~v1_funct_1(B_241))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2673])).
% 7.65/2.73  tff(c_2775, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_2759])).
% 7.65/2.73  tff(c_2798, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1213, c_1210, c_1210, c_1210, c_2775])).
% 7.65/2.73  tff(c_1214, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_185])).
% 7.65/2.73  tff(c_2822, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_1214])).
% 7.65/2.73  tff(c_2829, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_80, c_2822])).
% 7.65/2.73  tff(c_2835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_78, c_955, c_1096, c_1054, c_2829])).
% 7.65/2.73  tff(c_2837, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_239])).
% 7.65/2.73  tff(c_6, plain, (![A_5]: (k2_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.73  tff(c_163, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_140, c_6])).
% 7.65/2.73  tff(c_245, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_163])).
% 7.65/2.73  tff(c_2846, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2837, c_245])).
% 7.65/2.73  tff(c_2869, plain, (![B_245, A_246]: (k2_relat_1(B_245)=A_246 | ~v2_funct_2(B_245, A_246) | ~v5_relat_1(B_245, A_246) | ~v1_relat_1(B_245))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.65/2.73  tff(c_2878, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_2869])).
% 7.65/2.73  tff(c_2887, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2878])).
% 7.65/2.73  tff(c_3027, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2846, c_2887])).
% 7.65/2.73  tff(c_3243, plain, (![C_279, B_280, A_281]: (v2_funct_2(C_279, B_280) | ~v3_funct_2(C_279, A_281, B_280) | ~v1_funct_1(C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.65/2.73  tff(c_3253, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_3243])).
% 7.65/2.73  tff(c_3259, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_3253])).
% 7.65/2.73  tff(c_3261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3027, c_3259])).
% 7.65/2.73  tff(c_3262, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_163])).
% 7.65/2.73  tff(c_189, plain, (![A_61]: (k1_xboole_0!=A_61 | k6_partfun1(A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_177])).
% 7.65/2.73  tff(c_209, plain, (![A_61]: (k1_relat_1(k1_xboole_0)=A_61 | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_189, c_83])).
% 7.65/2.73  tff(c_3386, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3262, c_3262, c_209])).
% 7.65/2.73  tff(c_162, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_140, c_8])).
% 7.65/2.73  tff(c_221, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_162])).
% 7.65/2.73  tff(c_3264, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3262, c_221])).
% 7.65/2.73  tff(c_3389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3386, c_3264])).
% 7.65/2.73  tff(c_3390, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_162])).
% 7.65/2.73  tff(c_12, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.73  tff(c_82, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12])).
% 7.65/2.73  tff(c_180, plain, (![A_58]: (k2_relat_1(k6_partfun1(A_58))!=k1_xboole_0 | k6_partfun1(A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_174, c_6])).
% 7.65/2.73  tff(c_184, plain, (![A_58]: (k1_xboole_0!=A_58 | k6_partfun1(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_180])).
% 7.65/2.73  tff(c_3445, plain, (![A_299]: (A_299!='#skF_2' | k6_partfun1(A_299)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_3390, c_184])).
% 7.65/2.73  tff(c_3454, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3445, c_185])).
% 7.65/2.73  tff(c_3500, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_3454])).
% 7.65/2.73  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.65/2.73  tff(c_3398, plain, (![A_1]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_2])).
% 7.65/2.73  tff(c_3791, plain, (![C_336, B_337, A_338]: (v2_funct_2(C_336, B_337) | ~v3_funct_2(C_336, A_338, B_337) | ~v1_funct_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.65/2.73  tff(c_3795, plain, (![B_337, A_338]: (v2_funct_2('#skF_2', B_337) | ~v3_funct_2('#skF_2', A_338, B_337) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3398, c_3791])).
% 7.65/2.73  tff(c_3804, plain, (![B_339, A_340]: (v2_funct_2('#skF_2', B_339) | ~v3_funct_2('#skF_2', A_340, B_339))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3795])).
% 7.65/2.73  tff(c_3808, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_3804])).
% 7.65/2.73  tff(c_212, plain, (![A_61]: (k2_relat_1(k1_xboole_0)=A_61 | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_189, c_82])).
% 7.65/2.73  tff(c_3493, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_3390, c_212])).
% 7.65/2.73  tff(c_155, plain, (![B_56]: (v5_relat_1(k1_xboole_0, B_56))), inference(resolution, [status(thm)], [c_2, c_142])).
% 7.65/2.73  tff(c_3393, plain, (![B_56]: (v5_relat_1('#skF_2', B_56))), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_155])).
% 7.65/2.73  tff(c_3526, plain, (![B_309, A_310]: (k2_relat_1(B_309)=A_310 | ~v2_funct_2(B_309, A_310) | ~v5_relat_1(B_309, A_310) | ~v1_relat_1(B_309))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.65/2.73  tff(c_3529, plain, (![B_56]: (k2_relat_1('#skF_2')=B_56 | ~v2_funct_2('#skF_2', B_56) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3393, c_3526])).
% 7.65/2.73  tff(c_3535, plain, (![B_56]: (B_56='#skF_2' | ~v2_funct_2('#skF_2', B_56))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_3493, c_3529])).
% 7.65/2.73  tff(c_3811, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3808, c_3535])).
% 7.65/2.73  tff(c_3815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3500, c_3811])).
% 7.65/2.73  tff(c_3817, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3454])).
% 7.65/2.73  tff(c_3821, plain, (![A_1]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3398])).
% 7.65/2.73  tff(c_4327, plain, (![A_399, B_400, C_401, D_402]: (r2_relset_1(A_399, B_400, C_401, C_401) | ~m1_subset_1(D_402, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.65/2.73  tff(c_4386, plain, (![A_415, B_416, C_417]: (r2_relset_1(A_415, B_416, C_417, C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(resolution, [status(thm)], [c_3821, c_4327])).
% 7.65/2.73  tff(c_4392, plain, (![A_415, B_416]: (r2_relset_1(A_415, B_416, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_3821, c_4386])).
% 7.65/2.73  tff(c_3829, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_78])).
% 7.65/2.73  tff(c_3826, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_140])).
% 7.65/2.73  tff(c_4065, plain, (![C_364, A_365, B_366]: (v2_funct_1(C_364) | ~v3_funct_2(C_364, A_365, B_366) | ~v1_funct_1(C_364) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_365, B_366))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.65/2.73  tff(c_4069, plain, (![A_365, B_366]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_365, B_366) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3821, c_4065])).
% 7.65/2.73  tff(c_4075, plain, (![A_365, B_366]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_365, B_366))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_4069])).
% 7.65/2.73  tff(c_4081, plain, (![A_365, B_366]: (~v3_funct_2('#skF_1', A_365, B_366))), inference(splitLeft, [status(thm)], [c_4075])).
% 7.65/2.73  tff(c_3827, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_74])).
% 7.65/2.73  tff(c_4083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4081, c_3827])).
% 7.65/2.73  tff(c_4084, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_4075])).
% 7.65/2.73  tff(c_3443, plain, (![A_58]: (A_58!='#skF_2' | k6_partfun1(A_58)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_3390, c_184])).
% 7.65/2.73  tff(c_3897, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3817, c_3443])).
% 7.65/2.73  tff(c_3474, plain, (![A_299]: (k2_relat_1('#skF_2')=A_299 | A_299!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3445, c_82])).
% 7.65/2.73  tff(c_3940, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3817, c_3474])).
% 7.65/2.73  tff(c_3825, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3390])).
% 7.65/2.73  tff(c_18, plain, (![A_8]: (k2_funct_1(k6_relat_1(A_8))=k6_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.65/2.73  tff(c_79, plain, (![A_8]: (k2_funct_1(k6_partfun1(A_8))=k6_partfun1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_18])).
% 7.65/2.73  tff(c_203, plain, (![A_61]: (k6_partfun1(A_61)=k2_funct_1(k1_xboole_0) | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_189, c_79])).
% 7.65/2.73  tff(c_3989, plain, (![A_359]: (k6_partfun1(A_359)=k2_funct_1('#skF_1') | A_359!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3825, c_203])).
% 7.65/2.73  tff(c_4059, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3989, c_83])).
% 7.65/2.73  tff(c_139, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_62, c_128])).
% 7.65/2.73  tff(c_4009, plain, (![A_359]: (v1_relat_1(k2_funct_1('#skF_1')) | A_359!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3989, c_139])).
% 7.65/2.73  tff(c_4033, plain, (![A_359]: (A_359!='#skF_1')), inference(splitLeft, [status(thm)], [c_4009])).
% 7.65/2.73  tff(c_3391, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_162])).
% 7.65/2.73  tff(c_3413, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_3391])).
% 7.65/2.73  tff(c_3824, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3817, c_3413])).
% 7.65/2.73  tff(c_3952, plain, (![A_352, B_353, C_354]: (k1_relset_1(A_352, B_353, C_354)=k1_relat_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_352, B_353))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.65/2.73  tff(c_3956, plain, (![A_352, B_353]: (k1_relset_1(A_352, B_353, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_3821, c_3952])).
% 7.65/2.73  tff(c_3961, plain, (![A_352, B_353]: (k1_relset_1(A_352, B_353, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3956])).
% 7.65/2.73  tff(c_4040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4033, c_3961])).
% 7.65/2.73  tff(c_4041, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4009])).
% 7.65/2.73  tff(c_3395, plain, (![A_5]: (k1_relat_1(A_5)!='#skF_2' | A_5='#skF_2' | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3390, c_3390, c_8])).
% 7.65/2.73  tff(c_4144, plain, (![A_376]: (k1_relat_1(A_376)!='#skF_1' | A_376='#skF_1' | ~v1_relat_1(A_376))), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3817, c_3395])).
% 7.65/2.73  tff(c_4147, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4041, c_4144])).
% 7.65/2.73  tff(c_4156, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4059, c_4147])).
% 7.65/2.73  tff(c_4179, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4156, c_81])).
% 7.65/2.73  tff(c_4186, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_3829, c_4084, c_3897, c_3940, c_4179])).
% 7.65/2.73  tff(c_4635, plain, (![F_449, B_451, E_447, C_448, D_450, A_446]: (k1_partfun1(A_446, B_451, C_448, D_450, E_447, F_449)=k5_relat_1(E_447, F_449) | ~m1_subset_1(F_449, k1_zfmisc_1(k2_zfmisc_1(C_448, D_450))) | ~v1_funct_1(F_449) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(A_446, B_451))) | ~v1_funct_1(E_447))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.65/2.73  tff(c_4640, plain, (![B_451, E_447, C_448, D_450, A_446]: (k1_partfun1(A_446, B_451, C_448, D_450, E_447, '#skF_1')=k5_relat_1(E_447, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(A_446, B_451))) | ~v1_funct_1(E_447))), inference(resolution, [status(thm)], [c_3821, c_4635])).
% 7.65/2.73  tff(c_4657, plain, (![C_457, E_458, A_455, B_456, D_454]: (k1_partfun1(A_455, B_456, C_457, D_454, E_458, '#skF_1')=k5_relat_1(E_458, '#skF_1') | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))) | ~v1_funct_1(E_458))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_4640])).
% 7.65/2.73  tff(c_4662, plain, (![A_455, B_456, C_457, D_454]: (k1_partfun1(A_455, B_456, C_457, D_454, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3821, c_4657])).
% 7.65/2.73  tff(c_4668, plain, (![A_455, B_456, C_457, D_454]: (k1_partfun1(A_455, B_456, C_457, D_454, '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_4186, c_4662])).
% 7.65/2.73  tff(c_40, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.65/2.73  tff(c_4195, plain, (![C_377, B_378]: (v1_funct_2(C_377, '#skF_1', B_378) | k1_relset_1('#skF_1', B_378, C_377)!='#skF_1' | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_378))))), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3825, c_3825, c_3825, c_40])).
% 7.65/2.73  tff(c_4199, plain, (![B_378]: (v1_funct_2('#skF_1', '#skF_1', B_378) | k1_relset_1('#skF_1', B_378, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_3821, c_4195])).
% 7.65/2.73  tff(c_4206, plain, (![B_378]: (v1_funct_2('#skF_1', '#skF_1', B_378))), inference(demodulation, [status(thm), theory('equality')], [c_3961, c_4199])).
% 7.65/2.73  tff(c_4430, plain, (![A_424, B_425]: (k2_funct_2(A_424, B_425)=k2_funct_1(B_425) | ~m1_subset_1(B_425, k1_zfmisc_1(k2_zfmisc_1(A_424, A_424))) | ~v3_funct_2(B_425, A_424, A_424) | ~v1_funct_2(B_425, A_424, A_424) | ~v1_funct_1(B_425))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.65/2.73  tff(c_4434, plain, (![A_424]: (k2_funct_2(A_424, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_424, A_424) | ~v1_funct_2('#skF_1', A_424, A_424) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3821, c_4430])).
% 7.65/2.73  tff(c_4449, plain, (![A_427]: (k2_funct_2(A_427, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_427, A_427) | ~v1_funct_2('#skF_1', A_427, A_427))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_4156, c_4434])).
% 7.65/2.73  tff(c_4452, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3827, c_4449])).
% 7.65/2.73  tff(c_4455, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4206, c_4452])).
% 7.65/2.73  tff(c_3822, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_3817, c_185])).
% 7.65/2.73  tff(c_3938, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3897, c_3822])).
% 7.65/2.73  tff(c_4457, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4455, c_3938])).
% 7.65/2.73  tff(c_4670, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4668, c_4457])).
% 7.65/2.73  tff(c_4673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4392, c_4670])).
% 7.65/2.73  tff(c_4674, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_70])).
% 7.65/2.73  tff(c_5563, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5559, c_4674])).
% 7.65/2.73  tff(c_6169, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6138, c_5563])).
% 7.65/2.73  tff(c_6182, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_81, c_6169])).
% 7.65/2.73  tff(c_6188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_78, c_5320, c_5446, c_5138, c_6182])).
% 7.65/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.73  
% 7.65/2.73  Inference rules
% 7.65/2.73  ----------------------
% 7.65/2.73  #Ref     : 27
% 7.65/2.73  #Sup     : 1229
% 7.65/2.73  #Fact    : 0
% 7.65/2.73  #Define  : 0
% 7.65/2.73  #Split   : 36
% 7.65/2.73  #Chain   : 0
% 7.65/2.73  #Close   : 0
% 7.65/2.73  
% 7.65/2.73  Ordering : KBO
% 7.65/2.73  
% 7.65/2.73  Simplification rules
% 7.65/2.73  ----------------------
% 7.65/2.73  #Subsume      : 226
% 7.65/2.73  #Demod        : 1888
% 7.65/2.73  #Tautology    : 584
% 7.65/2.73  #SimpNegUnit  : 52
% 7.65/2.73  #BackRed      : 187
% 7.65/2.73  
% 7.65/2.74  #Partial instantiations: 0
% 7.65/2.74  #Strategies tried      : 1
% 7.65/2.74  
% 7.65/2.74  Timing (in seconds)
% 7.65/2.74  ----------------------
% 7.65/2.74  Preprocessing        : 0.37
% 7.65/2.74  Parsing              : 0.20
% 7.65/2.74  CNF conversion       : 0.02
% 7.65/2.74  Main loop            : 1.55
% 7.65/2.74  Inferencing          : 0.52
% 7.65/2.74  Reduction            : 0.60
% 7.65/2.74  Demodulation         : 0.44
% 7.65/2.74  BG Simplification    : 0.05
% 7.65/2.74  Subsumption          : 0.26
% 7.65/2.74  Abstraction          : 0.06
% 7.65/2.74  MUC search           : 0.00
% 7.65/2.74  Cooper               : 0.00
% 7.65/2.74  Total                : 1.99
% 7.65/2.74  Index Insertion      : 0.00
% 7.65/2.74  Index Deletion       : 0.00
% 7.65/2.74  Index Matching       : 0.00
% 7.65/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
