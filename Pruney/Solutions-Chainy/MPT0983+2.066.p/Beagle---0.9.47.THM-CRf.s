%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:10 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 379 expanded)
%              Number of leaves         :   45 ( 155 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 (1293 expanded)
%              Number of equality atoms :   49 ( 133 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_173,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_153,axiom,(
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

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_94,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_112,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_124,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_145,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_158,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_50,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_1549,plain,(
    ! [C_288,B_285,D_289,E_286,A_284,F_287] :
      ( k1_partfun1(A_284,B_285,C_288,D_289,E_286,F_287) = k5_relat_1(E_286,F_287)
      | ~ m1_subset_1(F_287,k1_zfmisc_1(k2_zfmisc_1(C_288,D_289)))
      | ~ v1_funct_1(F_287)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ v1_funct_1(E_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1553,plain,(
    ! [A_284,B_285,E_286] :
      ( k1_partfun1(A_284,B_285,'#skF_2','#skF_1',E_286,'#skF_4') = k5_relat_1(E_286,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ v1_funct_1(E_286) ) ),
    inference(resolution,[status(thm)],[c_58,c_1549])).

tff(c_1564,plain,(
    ! [A_292,B_293,E_294] :
      ( k1_partfun1(A_292,B_293,'#skF_2','#skF_1',E_294,'#skF_4') = k5_relat_1(E_294,'#skF_4')
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293)))
      | ~ v1_funct_1(E_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1553])).

tff(c_1573,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1564])).

tff(c_1580,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1573])).

tff(c_46,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1297,plain,(
    ! [D_240,C_241,A_242,B_243] :
      ( D_240 = C_241
      | ~ r2_relset_1(A_242,B_243,C_241,D_240)
      | ~ m1_subset_1(D_240,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1305,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_1297])).

tff(c_1320,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1305])).

tff(c_1329,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1320])).

tff(c_1587,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1580,c_1329])).

tff(c_1598,plain,(
    ! [B_296,E_297,D_295,C_300,A_298,F_299] :
      ( m1_subset_1(k1_partfun1(A_298,B_296,C_300,D_295,E_297,F_299),k1_zfmisc_1(k2_zfmisc_1(A_298,D_295)))
      | ~ m1_subset_1(F_299,k1_zfmisc_1(k2_zfmisc_1(C_300,D_295)))
      | ~ v1_funct_1(F_299)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(A_298,B_296)))
      | ~ v1_funct_1(E_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1628,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_1598])).

tff(c_1643,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1628])).

tff(c_1645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_1643])).

tff(c_1646,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1320])).

tff(c_1842,plain,(
    ! [B_330,E_331,A_329,C_333,F_332,D_334] :
      ( k1_partfun1(A_329,B_330,C_333,D_334,E_331,F_332) = k5_relat_1(E_331,F_332)
      | ~ m1_subset_1(F_332,k1_zfmisc_1(k2_zfmisc_1(C_333,D_334)))
      | ~ v1_funct_1(F_332)
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(E_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1846,plain,(
    ! [A_329,B_330,E_331] :
      ( k1_partfun1(A_329,B_330,'#skF_2','#skF_1',E_331,'#skF_4') = k5_relat_1(E_331,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(E_331) ) ),
    inference(resolution,[status(thm)],[c_58,c_1842])).

tff(c_1869,plain,(
    ! [A_339,B_340,E_341] :
      ( k1_partfun1(A_339,B_340,'#skF_2','#skF_1',E_341,'#skF_4') = k5_relat_1(E_341,'#skF_4')
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ v1_funct_1(E_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1846])).

tff(c_1878,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1869])).

tff(c_1885,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1646,c_1878])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1245,plain,(
    ! [B_232,A_233] :
      ( k1_relat_1(B_232) = A_233
      | ~ r1_tarski(A_233,k1_relat_1(B_232))
      | ~ v4_relat_1(B_232,A_233)
      | ~ v1_relat_1(B_232) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_1265,plain,(
    ! [A_5,B_7] :
      ( k1_relat_1(k5_relat_1(A_5,B_7)) = k1_relat_1(A_5)
      | ~ v4_relat_1(A_5,k1_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_1245])).

tff(c_1892,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_1265])).

tff(c_1904,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_123,c_158,c_71,c_71,c_1885,c_1892])).

tff(c_22,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_69,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_1661,plain,(
    ! [B_303,A_304] :
      ( r1_tarski(k2_relat_1(B_303),k1_relat_1(A_304))
      | k1_relat_1(k5_relat_1(B_303,A_304)) != k1_relat_1(B_303)
      | ~ v1_funct_1(B_303)
      | ~ v1_relat_1(B_303)
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v2_funct_1(B_14)
      | ~ r1_tarski(k2_relat_1(B_14),k1_relat_1(A_12))
      | ~ v2_funct_1(k5_relat_1(B_14,A_12))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2452,plain,(
    ! [B_367,A_368] :
      ( v2_funct_1(B_367)
      | ~ v2_funct_1(k5_relat_1(B_367,A_368))
      | k1_relat_1(k5_relat_1(B_367,A_368)) != k1_relat_1(B_367)
      | ~ v1_funct_1(B_367)
      | ~ v1_relat_1(B_367)
      | ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(resolution,[status(thm)],[c_1661,c_20])).

tff(c_2455,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_2452])).

tff(c_2457,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_62,c_124,c_68,c_1904,c_71,c_1885,c_69,c_2455])).

tff(c_2459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2457])).

tff(c_2460,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2472,plain,(
    ! [C_371,A_372,B_373] :
      ( v1_relat_1(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2483,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2472])).

tff(c_2542,plain,(
    ! [C_387,B_388,A_389] :
      ( v5_relat_1(C_387,B_388)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2553,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2542])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2618,plain,(
    ! [A_402,B_403,D_404] :
      ( r2_relset_1(A_402,B_403,D_404,D_404)
      | ~ m1_subset_1(D_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2625,plain,(
    ! [A_37] : r2_relset_1(A_37,A_37,k6_partfun1(A_37),k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_46,c_2618])).

tff(c_2629,plain,(
    ! [A_406,B_407,C_408] :
      ( k2_relset_1(A_406,B_407,C_408) = k2_relat_1(C_408)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2641,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2629])).

tff(c_2936,plain,(
    ! [F_467,D_469,C_468,E_466,A_464,B_465] :
      ( k1_partfun1(A_464,B_465,C_468,D_469,E_466,F_467) = k5_relat_1(E_466,F_467)
      | ~ m1_subset_1(F_467,k1_zfmisc_1(k2_zfmisc_1(C_468,D_469)))
      | ~ v1_funct_1(F_467)
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465)))
      | ~ v1_funct_1(E_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2940,plain,(
    ! [A_464,B_465,E_466] :
      ( k1_partfun1(A_464,B_465,'#skF_2','#skF_1',E_466,'#skF_4') = k5_relat_1(E_466,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465)))
      | ~ v1_funct_1(E_466) ) ),
    inference(resolution,[status(thm)],[c_58,c_2936])).

tff(c_2953,plain,(
    ! [A_474,B_475,E_476] :
      ( k1_partfun1(A_474,B_475,'#skF_2','#skF_1',E_476,'#skF_4') = k5_relat_1(E_476,'#skF_4')
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(A_474,B_475)))
      | ~ v1_funct_1(E_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2940])).

tff(c_2962,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2953])).

tff(c_2969,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2962])).

tff(c_2792,plain,(
    ! [D_428,C_429,A_430,B_431] :
      ( D_428 = C_429
      | ~ r2_relset_1(A_430,B_431,C_429,D_428)
      | ~ m1_subset_1(D_428,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431)))
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2800,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_2792])).

tff(c_2815,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2800])).

tff(c_2857,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2815])).

tff(c_2976,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2969,c_2857])).

tff(c_2987,plain,(
    ! [F_481,C_482,E_479,B_478,A_480,D_477] :
      ( m1_subset_1(k1_partfun1(A_480,B_478,C_482,D_477,E_479,F_481),k1_zfmisc_1(k2_zfmisc_1(A_480,D_477)))
      | ~ m1_subset_1(F_481,k1_zfmisc_1(k2_zfmisc_1(C_482,D_477)))
      | ~ v1_funct_1(F_481)
      | ~ m1_subset_1(E_479,k1_zfmisc_1(k2_zfmisc_1(A_480,B_478)))
      | ~ v1_funct_1(E_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3019,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2969,c_2987])).

tff(c_3035,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_3019])).

tff(c_3038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2976,c_3035])).

tff(c_3039,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2815])).

tff(c_3467,plain,(
    ! [A_531,B_532,C_533,D_534] :
      ( k2_relset_1(A_531,B_532,C_533) = B_532
      | ~ r2_relset_1(B_532,B_532,k1_partfun1(B_532,A_531,A_531,B_532,D_534,C_533),k6_partfun1(B_532))
      | ~ m1_subset_1(D_534,k1_zfmisc_1(k2_zfmisc_1(B_532,A_531)))
      | ~ v1_funct_2(D_534,B_532,A_531)
      | ~ v1_funct_1(D_534)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532)))
      | ~ v1_funct_2(C_533,A_531,B_532)
      | ~ v1_funct_1(C_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3470,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3039,c_3467])).

tff(c_3472,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2625,c_2641,c_3470])).

tff(c_36,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3483,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3472,c_36])).

tff(c_3491,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2483,c_2553,c_3472,c_3483])).

tff(c_3493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2460,c_3491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.06  
% 5.60/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.06  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.60/2.06  
% 5.60/2.06  %Foreground sorts:
% 5.60/2.06  
% 5.60/2.06  
% 5.60/2.06  %Background operators:
% 5.60/2.06  
% 5.60/2.06  
% 5.60/2.06  %Foreground operators:
% 5.60/2.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.60/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.06  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.60/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.60/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.60/2.06  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.60/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.60/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.60/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.60/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.06  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.60/2.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.60/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.06  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.60/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.60/2.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.60/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.60/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.06  
% 5.75/2.08  tff(f_173, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.75/2.08  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.75/2.08  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.75/2.08  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.75/2.08  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.75/2.08  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.75/2.08  tff(f_124, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.75/2.08  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.75/2.08  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.75/2.08  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 5.75/2.08  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.75/2.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.75/2.08  tff(f_78, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 5.75/2.08  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 5.75/2.08  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 5.75/2.08  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.08  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.75/2.08  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.75/2.08  tff(c_54, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_94, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 5.75/2.08  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_112, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.08  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_112])).
% 5.75/2.08  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_124, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_112])).
% 5.75/2.08  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_145, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.75/2.08  tff(c_158, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_145])).
% 5.75/2.08  tff(c_50, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.08  tff(c_14, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.08  tff(c_71, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 5.75/2.08  tff(c_1549, plain, (![C_288, B_285, D_289, E_286, A_284, F_287]: (k1_partfun1(A_284, B_285, C_288, D_289, E_286, F_287)=k5_relat_1(E_286, F_287) | ~m1_subset_1(F_287, k1_zfmisc_1(k2_zfmisc_1(C_288, D_289))) | ~v1_funct_1(F_287) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~v1_funct_1(E_286))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.75/2.08  tff(c_1553, plain, (![A_284, B_285, E_286]: (k1_partfun1(A_284, B_285, '#skF_2', '#skF_1', E_286, '#skF_4')=k5_relat_1(E_286, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~v1_funct_1(E_286))), inference(resolution, [status(thm)], [c_58, c_1549])).
% 5.75/2.08  tff(c_1564, plain, (![A_292, B_293, E_294]: (k1_partfun1(A_292, B_293, '#skF_2', '#skF_1', E_294, '#skF_4')=k5_relat_1(E_294, '#skF_4') | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))) | ~v1_funct_1(E_294))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1553])).
% 5.75/2.08  tff(c_1573, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1564])).
% 5.75/2.08  tff(c_1580, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1573])).
% 5.75/2.08  tff(c_46, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.75/2.08  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_1297, plain, (![D_240, C_241, A_242, B_243]: (D_240=C_241 | ~r2_relset_1(A_242, B_243, C_241, D_240) | ~m1_subset_1(D_240, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.08  tff(c_1305, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_1297])).
% 5.75/2.08  tff(c_1320, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1305])).
% 5.75/2.08  tff(c_1329, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1320])).
% 5.75/2.08  tff(c_1587, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1580, c_1329])).
% 5.75/2.08  tff(c_1598, plain, (![B_296, E_297, D_295, C_300, A_298, F_299]: (m1_subset_1(k1_partfun1(A_298, B_296, C_300, D_295, E_297, F_299), k1_zfmisc_1(k2_zfmisc_1(A_298, D_295))) | ~m1_subset_1(F_299, k1_zfmisc_1(k2_zfmisc_1(C_300, D_295))) | ~v1_funct_1(F_299) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(A_298, B_296))) | ~v1_funct_1(E_297))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.75/2.08  tff(c_1628, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1580, c_1598])).
% 5.75/2.08  tff(c_1643, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1628])).
% 5.75/2.08  tff(c_1645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1587, c_1643])).
% 5.75/2.08  tff(c_1646, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1320])).
% 5.75/2.08  tff(c_1842, plain, (![B_330, E_331, A_329, C_333, F_332, D_334]: (k1_partfun1(A_329, B_330, C_333, D_334, E_331, F_332)=k5_relat_1(E_331, F_332) | ~m1_subset_1(F_332, k1_zfmisc_1(k2_zfmisc_1(C_333, D_334))) | ~v1_funct_1(F_332) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(E_331))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.75/2.08  tff(c_1846, plain, (![A_329, B_330, E_331]: (k1_partfun1(A_329, B_330, '#skF_2', '#skF_1', E_331, '#skF_4')=k5_relat_1(E_331, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(E_331))), inference(resolution, [status(thm)], [c_58, c_1842])).
% 5.75/2.08  tff(c_1869, plain, (![A_339, B_340, E_341]: (k1_partfun1(A_339, B_340, '#skF_2', '#skF_1', E_341, '#skF_4')=k5_relat_1(E_341, '#skF_4') | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~v1_funct_1(E_341))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1846])).
% 5.75/2.08  tff(c_1878, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1869])).
% 5.75/2.08  tff(c_1885, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1646, c_1878])).
% 5.75/2.08  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.75/2.08  tff(c_173, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.75/2.08  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.75/2.08  tff(c_1245, plain, (![B_232, A_233]: (k1_relat_1(B_232)=A_233 | ~r1_tarski(A_233, k1_relat_1(B_232)) | ~v4_relat_1(B_232, A_233) | ~v1_relat_1(B_232))), inference(resolution, [status(thm)], [c_173, c_2])).
% 5.75/2.08  tff(c_1265, plain, (![A_5, B_7]: (k1_relat_1(k5_relat_1(A_5, B_7))=k1_relat_1(A_5) | ~v4_relat_1(A_5, k1_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_1245])).
% 5.75/2.08  tff(c_1892, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1885, c_1265])).
% 5.75/2.08  tff(c_1904, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_123, c_158, c_71, c_71, c_1885, c_1892])).
% 5.75/2.08  tff(c_22, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.75/2.08  tff(c_69, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 5.75/2.08  tff(c_1661, plain, (![B_303, A_304]: (r1_tarski(k2_relat_1(B_303), k1_relat_1(A_304)) | k1_relat_1(k5_relat_1(B_303, A_304))!=k1_relat_1(B_303) | ~v1_funct_1(B_303) | ~v1_relat_1(B_303) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.75/2.08  tff(c_20, plain, (![B_14, A_12]: (v2_funct_1(B_14) | ~r1_tarski(k2_relat_1(B_14), k1_relat_1(A_12)) | ~v2_funct_1(k5_relat_1(B_14, A_12)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.75/2.08  tff(c_2452, plain, (![B_367, A_368]: (v2_funct_1(B_367) | ~v2_funct_1(k5_relat_1(B_367, A_368)) | k1_relat_1(k5_relat_1(B_367, A_368))!=k1_relat_1(B_367) | ~v1_funct_1(B_367) | ~v1_relat_1(B_367) | ~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(resolution, [status(thm)], [c_1661, c_20])).
% 5.75/2.08  tff(c_2455, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1885, c_2452])).
% 5.75/2.08  tff(c_2457, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_62, c_124, c_68, c_1904, c_71, c_1885, c_69, c_2455])).
% 5.75/2.08  tff(c_2459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_2457])).
% 5.75/2.08  tff(c_2460, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 5.75/2.08  tff(c_2472, plain, (![C_371, A_372, B_373]: (v1_relat_1(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.08  tff(c_2483, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2472])).
% 5.75/2.08  tff(c_2542, plain, (![C_387, B_388, A_389]: (v5_relat_1(C_387, B_388) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.75/2.08  tff(c_2553, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2542])).
% 5.75/2.08  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.75/2.08  tff(c_2618, plain, (![A_402, B_403, D_404]: (r2_relset_1(A_402, B_403, D_404, D_404) | ~m1_subset_1(D_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.08  tff(c_2625, plain, (![A_37]: (r2_relset_1(A_37, A_37, k6_partfun1(A_37), k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_46, c_2618])).
% 5.75/2.08  tff(c_2629, plain, (![A_406, B_407, C_408]: (k2_relset_1(A_406, B_407, C_408)=k2_relat_1(C_408) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.75/2.08  tff(c_2641, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2629])).
% 5.75/2.08  tff(c_2936, plain, (![F_467, D_469, C_468, E_466, A_464, B_465]: (k1_partfun1(A_464, B_465, C_468, D_469, E_466, F_467)=k5_relat_1(E_466, F_467) | ~m1_subset_1(F_467, k1_zfmisc_1(k2_zfmisc_1(C_468, D_469))) | ~v1_funct_1(F_467) | ~m1_subset_1(E_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))) | ~v1_funct_1(E_466))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.75/2.08  tff(c_2940, plain, (![A_464, B_465, E_466]: (k1_partfun1(A_464, B_465, '#skF_2', '#skF_1', E_466, '#skF_4')=k5_relat_1(E_466, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))) | ~v1_funct_1(E_466))), inference(resolution, [status(thm)], [c_58, c_2936])).
% 5.75/2.08  tff(c_2953, plain, (![A_474, B_475, E_476]: (k1_partfun1(A_474, B_475, '#skF_2', '#skF_1', E_476, '#skF_4')=k5_relat_1(E_476, '#skF_4') | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(A_474, B_475))) | ~v1_funct_1(E_476))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2940])).
% 5.75/2.08  tff(c_2962, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2953])).
% 5.75/2.08  tff(c_2969, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2962])).
% 5.75/2.08  tff(c_2792, plain, (![D_428, C_429, A_430, B_431]: (D_428=C_429 | ~r2_relset_1(A_430, B_431, C_429, D_428) | ~m1_subset_1(D_428, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.08  tff(c_2800, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_2792])).
% 5.75/2.08  tff(c_2815, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2800])).
% 5.75/2.08  tff(c_2857, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2815])).
% 5.75/2.08  tff(c_2976, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2969, c_2857])).
% 5.75/2.08  tff(c_2987, plain, (![F_481, C_482, E_479, B_478, A_480, D_477]: (m1_subset_1(k1_partfun1(A_480, B_478, C_482, D_477, E_479, F_481), k1_zfmisc_1(k2_zfmisc_1(A_480, D_477))) | ~m1_subset_1(F_481, k1_zfmisc_1(k2_zfmisc_1(C_482, D_477))) | ~v1_funct_1(F_481) | ~m1_subset_1(E_479, k1_zfmisc_1(k2_zfmisc_1(A_480, B_478))) | ~v1_funct_1(E_479))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.75/2.08  tff(c_3019, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2969, c_2987])).
% 5.75/2.08  tff(c_3035, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_3019])).
% 5.75/2.08  tff(c_3038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2976, c_3035])).
% 5.75/2.08  tff(c_3039, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2815])).
% 5.75/2.08  tff(c_3467, plain, (![A_531, B_532, C_533, D_534]: (k2_relset_1(A_531, B_532, C_533)=B_532 | ~r2_relset_1(B_532, B_532, k1_partfun1(B_532, A_531, A_531, B_532, D_534, C_533), k6_partfun1(B_532)) | ~m1_subset_1(D_534, k1_zfmisc_1(k2_zfmisc_1(B_532, A_531))) | ~v1_funct_2(D_534, B_532, A_531) | ~v1_funct_1(D_534) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_531, B_532))) | ~v1_funct_2(C_533, A_531, B_532) | ~v1_funct_1(C_533))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.75/2.08  tff(c_3470, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3039, c_3467])).
% 5.75/2.08  tff(c_3472, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2625, c_2641, c_3470])).
% 5.75/2.08  tff(c_36, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.08  tff(c_3483, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3472, c_36])).
% 5.75/2.08  tff(c_3491, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2483, c_2553, c_3472, c_3483])).
% 5.75/2.08  tff(c_3493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2460, c_3491])).
% 5.75/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.08  
% 5.75/2.08  Inference rules
% 5.75/2.08  ----------------------
% 5.75/2.08  #Ref     : 0
% 5.75/2.08  #Sup     : 697
% 5.75/2.08  #Fact    : 0
% 5.75/2.08  #Define  : 0
% 5.75/2.08  #Split   : 9
% 5.75/2.08  #Chain   : 0
% 5.75/2.08  #Close   : 0
% 5.75/2.08  
% 5.75/2.08  Ordering : KBO
% 5.75/2.08  
% 5.75/2.08  Simplification rules
% 5.75/2.08  ----------------------
% 5.75/2.08  #Subsume      : 55
% 5.75/2.08  #Demod        : 699
% 5.75/2.08  #Tautology    : 194
% 5.75/2.08  #SimpNegUnit  : 5
% 5.75/2.08  #BackRed      : 20
% 5.75/2.08  
% 5.75/2.08  #Partial instantiations: 0
% 5.75/2.08  #Strategies tried      : 1
% 5.75/2.08  
% 5.75/2.08  Timing (in seconds)
% 5.75/2.08  ----------------------
% 5.75/2.09  Preprocessing        : 0.37
% 5.75/2.09  Parsing              : 0.20
% 5.75/2.09  CNF conversion       : 0.03
% 5.75/2.09  Main loop            : 0.92
% 5.75/2.09  Inferencing          : 0.35
% 5.75/2.09  Reduction            : 0.31
% 5.75/2.09  Demodulation         : 0.23
% 5.75/2.09  BG Simplification    : 0.04
% 5.75/2.09  Subsumption          : 0.15
% 5.75/2.09  Abstraction          : 0.05
% 5.75/2.09  MUC search           : 0.00
% 5.75/2.09  Cooper               : 0.00
% 5.75/2.09  Total                : 1.33
% 5.75/2.09  Index Insertion      : 0.00
% 5.75/2.09  Index Deletion       : 0.00
% 5.75/2.09  Index Matching       : 0.00
% 5.75/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
