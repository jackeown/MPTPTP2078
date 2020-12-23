%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:10 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 380 expanded)
%              Number of leaves         :   45 ( 155 expanded)
%              Depth                    :    9
%              Number of atoms          :  279 (1296 expanded)
%              Number of equality atoms :   51 ( 135 expanded)
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

tff(f_175,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_109,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_121,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_122,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_109])).

tff(c_163,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_175,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_163])).

tff(c_52,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_14,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1486,plain,(
    ! [C_285,F_284,E_283,D_286,A_281,B_282] :
      ( k1_partfun1(A_281,B_282,C_285,D_286,E_283,F_284) = k5_relat_1(E_283,F_284)
      | ~ m1_subset_1(F_284,k1_zfmisc_1(k2_zfmisc_1(C_285,D_286)))
      | ~ v1_funct_1(F_284)
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(E_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1492,plain,(
    ! [A_281,B_282,E_283] :
      ( k1_partfun1(A_281,B_282,'#skF_2','#skF_1',E_283,'#skF_4') = k5_relat_1(E_283,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(E_283) ) ),
    inference(resolution,[status(thm)],[c_60,c_1486])).

tff(c_1528,plain,(
    ! [A_291,B_292,E_293] :
      ( k1_partfun1(A_291,B_292,'#skF_2','#skF_1',E_293,'#skF_4') = k5_relat_1(E_293,'#skF_4')
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(E_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1492])).

tff(c_1534,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1528])).

tff(c_1541,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1534])).

tff(c_48,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1258,plain,(
    ! [D_235,C_236,A_237,B_238] :
      ( D_235 = C_236
      | ~ r2_relset_1(A_237,B_238,C_236,D_235)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1266,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1258])).

tff(c_1281,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1266])).

tff(c_1350,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1546,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1350])).

tff(c_1552,plain,(
    ! [E_296,C_299,D_294,F_298,A_297,B_295] :
      ( m1_subset_1(k1_partfun1(A_297,B_295,C_299,D_294,E_296,F_298),k1_zfmisc_1(k2_zfmisc_1(A_297,D_294)))
      | ~ m1_subset_1(F_298,k1_zfmisc_1(k2_zfmisc_1(C_299,D_294)))
      | ~ v1_funct_1(F_298)
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(A_297,B_295)))
      | ~ v1_funct_1(E_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1585,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_1552])).

tff(c_1604,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1585])).

tff(c_1614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_1604])).

tff(c_1615,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1759,plain,(
    ! [A_336,D_341,F_339,C_340,E_338,B_337] :
      ( k1_partfun1(A_336,B_337,C_340,D_341,E_338,F_339) = k5_relat_1(E_338,F_339)
      | ~ m1_subset_1(F_339,k1_zfmisc_1(k2_zfmisc_1(C_340,D_341)))
      | ~ v1_funct_1(F_339)
      | ~ m1_subset_1(E_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ v1_funct_1(E_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1765,plain,(
    ! [A_336,B_337,E_338] :
      ( k1_partfun1(A_336,B_337,'#skF_2','#skF_1',E_338,'#skF_4') = k5_relat_1(E_338,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ v1_funct_1(E_338) ) ),
    inference(resolution,[status(thm)],[c_60,c_1759])).

tff(c_1813,plain,(
    ! [A_346,B_347,E_348] :
      ( k1_partfun1(A_346,B_347,'#skF_2','#skF_1',E_348,'#skF_4') = k5_relat_1(E_348,'#skF_4')
      | ~ m1_subset_1(E_348,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347)))
      | ~ v1_funct_1(E_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1765])).

tff(c_1819,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1813])).

tff(c_1826,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1615,c_1819])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_177,plain,(
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

tff(c_1164,plain,(
    ! [B_221,A_222] :
      ( k1_relat_1(B_221) = A_222
      | ~ r1_tarski(A_222,k1_relat_1(B_221))
      | ~ v4_relat_1(B_221,A_222)
      | ~ v1_relat_1(B_221) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_1188,plain,(
    ! [A_5,B_7] :
      ( k1_relat_1(k5_relat_1(A_5,B_7)) = k1_relat_1(A_5)
      | ~ v4_relat_1(A_5,k1_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_1164])).

tff(c_1901,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1826,c_1188])).

tff(c_1916,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_122,c_175,c_74,c_74,c_1826,c_1901])).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_107,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_20,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_22,plain,(
    ! [B_12,A_10] :
      ( r1_tarski(k2_relat_1(B_12),k1_relat_1(A_10))
      | k1_relat_1(k5_relat_1(B_12,A_10)) != k1_relat_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1653,plain,(
    ! [B_306,A_307] :
      ( v2_funct_1(B_306)
      | ~ r1_tarski(k2_relat_1(B_306),k1_relat_1(A_307))
      | ~ v2_funct_1(k5_relat_1(B_306,A_307))
      | ~ v1_funct_1(B_306)
      | ~ v1_relat_1(B_306)
      | ~ v1_funct_1(A_307)
      | ~ v1_relat_1(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1666,plain,(
    ! [B_12,A_10] :
      ( v2_funct_1(B_12)
      | ~ v2_funct_1(k5_relat_1(B_12,A_10))
      | k1_relat_1(k5_relat_1(B_12,A_10)) != k1_relat_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_22,c_1653])).

tff(c_1895,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1826,c_1666])).

tff(c_1911,plain,
    ( v2_funct_1('#skF_3')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_64,c_121,c_70,c_74,c_1826,c_71,c_1895])).

tff(c_1912,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1911])).

tff(c_2001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1912])).

tff(c_2002,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2012,plain,(
    ! [C_358,A_359,B_360] :
      ( v1_relat_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2025,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2012])).

tff(c_2075,plain,(
    ! [C_371,B_372,A_373] :
      ( v5_relat_1(C_371,B_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2087,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2075])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2151,plain,(
    ! [A_386,B_387,D_388] :
      ( r2_relset_1(A_386,B_387,D_388,D_388)
      | ~ m1_subset_1(D_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2158,plain,(
    ! [A_37] : r2_relset_1(A_37,A_37,k6_partfun1(A_37),k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_48,c_2151])).

tff(c_2162,plain,(
    ! [A_390,B_391,C_392] :
      ( k2_relset_1(A_390,B_391,C_392) = k2_relat_1(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2175,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2162])).

tff(c_2468,plain,(
    ! [F_449,C_450,E_448,B_447,D_451,A_446] :
      ( k1_partfun1(A_446,B_447,C_450,D_451,E_448,F_449) = k5_relat_1(E_448,F_449)
      | ~ m1_subset_1(F_449,k1_zfmisc_1(k2_zfmisc_1(C_450,D_451)))
      | ~ v1_funct_1(F_449)
      | ~ m1_subset_1(E_448,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ v1_funct_1(E_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2474,plain,(
    ! [A_446,B_447,E_448] :
      ( k1_partfun1(A_446,B_447,'#skF_2','#skF_1',E_448,'#skF_4') = k5_relat_1(E_448,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_448,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ v1_funct_1(E_448) ) ),
    inference(resolution,[status(thm)],[c_60,c_2468])).

tff(c_2485,plain,(
    ! [A_456,B_457,E_458] :
      ( k1_partfun1(A_456,B_457,'#skF_2','#skF_1',E_458,'#skF_4') = k5_relat_1(E_458,'#skF_4')
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ v1_funct_1(E_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2474])).

tff(c_2491,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2485])).

tff(c_2498,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2491])).

tff(c_2230,plain,(
    ! [D_398,C_399,A_400,B_401] :
      ( D_398 = C_399
      | ~ r2_relset_1(A_400,B_401,C_399,D_398)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2238,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2230])).

tff(c_2253,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2238])).

tff(c_2389,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2253])).

tff(c_2503,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_2389])).

tff(c_2519,plain,(
    ! [F_463,C_464,D_459,B_460,A_462,E_461] :
      ( m1_subset_1(k1_partfun1(A_462,B_460,C_464,D_459,E_461,F_463),k1_zfmisc_1(k2_zfmisc_1(A_462,D_459)))
      | ~ m1_subset_1(F_463,k1_zfmisc_1(k2_zfmisc_1(C_464,D_459)))
      | ~ v1_funct_1(F_463)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(A_462,B_460)))
      | ~ v1_funct_1(E_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2554,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2498,c_2519])).

tff(c_2569,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2554])).

tff(c_2571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2503,c_2569])).

tff(c_2572,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2253])).

tff(c_2904,plain,(
    ! [A_500,B_501,C_502,D_503] :
      ( k2_relset_1(A_500,B_501,C_502) = B_501
      | ~ r2_relset_1(B_501,B_501,k1_partfun1(B_501,A_500,A_500,B_501,D_503,C_502),k6_partfun1(B_501))
      | ~ m1_subset_1(D_503,k1_zfmisc_1(k2_zfmisc_1(B_501,A_500)))
      | ~ v1_funct_2(D_503,B_501,A_500)
      | ~ v1_funct_1(D_503)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_500,B_501)))
      | ~ v1_funct_2(C_502,A_500,B_501)
      | ~ v1_funct_1(C_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2910,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2572,c_2904])).

tff(c_2914,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_2158,c_2175,c_2910])).

tff(c_38,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2925,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_38])).

tff(c_2933,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2025,c_2087,c_2914,c_2925])).

tff(c_2935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2002,c_2933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.94  
% 5.10/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.94  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.10/1.94  
% 5.10/1.94  %Foreground sorts:
% 5.10/1.94  
% 5.10/1.94  
% 5.10/1.94  %Background operators:
% 5.10/1.94  
% 5.10/1.94  
% 5.10/1.94  %Foreground operators:
% 5.10/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.10/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.10/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.10/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.10/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/1.94  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.10/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.10/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.10/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.10/1.94  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.10/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.10/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.10/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.10/1.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.10/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.10/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.94  
% 5.10/1.97  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.10/1.97  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.10/1.97  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.10/1.97  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.10/1.97  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.10/1.97  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.10/1.97  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.10/1.97  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.10/1.97  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.10/1.97  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 5.10/1.97  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.10/1.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.10/1.97  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.10/1.97  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 5.10/1.97  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 5.10/1.97  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.10/1.97  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.10/1.97  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.10/1.97  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_109, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.10/1.97  tff(c_121, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_109])).
% 5.10/1.97  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_122, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_109])).
% 5.10/1.97  tff(c_163, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.10/1.97  tff(c_175, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_163])).
% 5.10/1.97  tff(c_52, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.10/1.97  tff(c_14, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.10/1.97  tff(c_74, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14])).
% 5.10/1.97  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_1486, plain, (![C_285, F_284, E_283, D_286, A_281, B_282]: (k1_partfun1(A_281, B_282, C_285, D_286, E_283, F_284)=k5_relat_1(E_283, F_284) | ~m1_subset_1(F_284, k1_zfmisc_1(k2_zfmisc_1(C_285, D_286))) | ~v1_funct_1(F_284) | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(E_283))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.10/1.97  tff(c_1492, plain, (![A_281, B_282, E_283]: (k1_partfun1(A_281, B_282, '#skF_2', '#skF_1', E_283, '#skF_4')=k5_relat_1(E_283, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(E_283))), inference(resolution, [status(thm)], [c_60, c_1486])).
% 5.10/1.97  tff(c_1528, plain, (![A_291, B_292, E_293]: (k1_partfun1(A_291, B_292, '#skF_2', '#skF_1', E_293, '#skF_4')=k5_relat_1(E_293, '#skF_4') | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(E_293))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1492])).
% 5.10/1.97  tff(c_1534, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1528])).
% 5.10/1.97  tff(c_1541, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1534])).
% 5.10/1.97  tff(c_48, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.10/1.97  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_1258, plain, (![D_235, C_236, A_237, B_238]: (D_235=C_236 | ~r2_relset_1(A_237, B_238, C_236, D_235) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.10/1.97  tff(c_1266, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1258])).
% 5.10/1.97  tff(c_1281, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1266])).
% 5.10/1.97  tff(c_1350, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1281])).
% 5.10/1.97  tff(c_1546, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1350])).
% 5.10/1.97  tff(c_1552, plain, (![E_296, C_299, D_294, F_298, A_297, B_295]: (m1_subset_1(k1_partfun1(A_297, B_295, C_299, D_294, E_296, F_298), k1_zfmisc_1(k2_zfmisc_1(A_297, D_294))) | ~m1_subset_1(F_298, k1_zfmisc_1(k2_zfmisc_1(C_299, D_294))) | ~v1_funct_1(F_298) | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(A_297, B_295))) | ~v1_funct_1(E_296))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.10/1.97  tff(c_1585, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1541, c_1552])).
% 5.10/1.97  tff(c_1604, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1585])).
% 5.10/1.97  tff(c_1614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1546, c_1604])).
% 5.10/1.97  tff(c_1615, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1281])).
% 5.10/1.97  tff(c_1759, plain, (![A_336, D_341, F_339, C_340, E_338, B_337]: (k1_partfun1(A_336, B_337, C_340, D_341, E_338, F_339)=k5_relat_1(E_338, F_339) | ~m1_subset_1(F_339, k1_zfmisc_1(k2_zfmisc_1(C_340, D_341))) | ~v1_funct_1(F_339) | ~m1_subset_1(E_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~v1_funct_1(E_338))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.10/1.97  tff(c_1765, plain, (![A_336, B_337, E_338]: (k1_partfun1(A_336, B_337, '#skF_2', '#skF_1', E_338, '#skF_4')=k5_relat_1(E_338, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~v1_funct_1(E_338))), inference(resolution, [status(thm)], [c_60, c_1759])).
% 5.10/1.97  tff(c_1813, plain, (![A_346, B_347, E_348]: (k1_partfun1(A_346, B_347, '#skF_2', '#skF_1', E_348, '#skF_4')=k5_relat_1(E_348, '#skF_4') | ~m1_subset_1(E_348, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))) | ~v1_funct_1(E_348))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1765])).
% 5.10/1.97  tff(c_1819, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1813])).
% 5.10/1.97  tff(c_1826, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1615, c_1819])).
% 5.10/1.97  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.10/1.97  tff(c_177, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/1.97  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/1.97  tff(c_1164, plain, (![B_221, A_222]: (k1_relat_1(B_221)=A_222 | ~r1_tarski(A_222, k1_relat_1(B_221)) | ~v4_relat_1(B_221, A_222) | ~v1_relat_1(B_221))), inference(resolution, [status(thm)], [c_177, c_2])).
% 5.10/1.97  tff(c_1188, plain, (![A_5, B_7]: (k1_relat_1(k5_relat_1(A_5, B_7))=k1_relat_1(A_5) | ~v4_relat_1(A_5, k1_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_1164])).
% 5.10/1.97  tff(c_1901, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1826, c_1188])).
% 5.10/1.97  tff(c_1916, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_122, c_175, c_74, c_74, c_1826, c_1901])).
% 5.10/1.97  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_107, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 5.10/1.97  tff(c_20, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.10/1.97  tff(c_71, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 5.10/1.97  tff(c_22, plain, (![B_12, A_10]: (r1_tarski(k2_relat_1(B_12), k1_relat_1(A_10)) | k1_relat_1(k5_relat_1(B_12, A_10))!=k1_relat_1(B_12) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.10/1.97  tff(c_1653, plain, (![B_306, A_307]: (v2_funct_1(B_306) | ~r1_tarski(k2_relat_1(B_306), k1_relat_1(A_307)) | ~v2_funct_1(k5_relat_1(B_306, A_307)) | ~v1_funct_1(B_306) | ~v1_relat_1(B_306) | ~v1_funct_1(A_307) | ~v1_relat_1(A_307))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.10/1.97  tff(c_1666, plain, (![B_12, A_10]: (v2_funct_1(B_12) | ~v2_funct_1(k5_relat_1(B_12, A_10)) | k1_relat_1(k5_relat_1(B_12, A_10))!=k1_relat_1(B_12) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_22, c_1653])).
% 5.10/1.97  tff(c_1895, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1826, c_1666])).
% 5.10/1.97  tff(c_1911, plain, (v2_funct_1('#skF_3') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_64, c_121, c_70, c_74, c_1826, c_71, c_1895])).
% 5.10/1.97  tff(c_1912, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_107, c_1911])).
% 5.10/1.97  tff(c_2001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1912])).
% 5.10/1.97  tff(c_2002, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 5.10/1.97  tff(c_2012, plain, (![C_358, A_359, B_360]: (v1_relat_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.10/1.97  tff(c_2025, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2012])).
% 5.10/1.97  tff(c_2075, plain, (![C_371, B_372, A_373]: (v5_relat_1(C_371, B_372) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.10/1.97  tff(c_2087, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_2075])).
% 5.10/1.97  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.10/1.97  tff(c_2151, plain, (![A_386, B_387, D_388]: (r2_relset_1(A_386, B_387, D_388, D_388) | ~m1_subset_1(D_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.10/1.97  tff(c_2158, plain, (![A_37]: (r2_relset_1(A_37, A_37, k6_partfun1(A_37), k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_48, c_2151])).
% 5.10/1.97  tff(c_2162, plain, (![A_390, B_391, C_392]: (k2_relset_1(A_390, B_391, C_392)=k2_relat_1(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.10/1.97  tff(c_2175, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2162])).
% 5.10/1.97  tff(c_2468, plain, (![F_449, C_450, E_448, B_447, D_451, A_446]: (k1_partfun1(A_446, B_447, C_450, D_451, E_448, F_449)=k5_relat_1(E_448, F_449) | ~m1_subset_1(F_449, k1_zfmisc_1(k2_zfmisc_1(C_450, D_451))) | ~v1_funct_1(F_449) | ~m1_subset_1(E_448, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~v1_funct_1(E_448))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.10/1.97  tff(c_2474, plain, (![A_446, B_447, E_448]: (k1_partfun1(A_446, B_447, '#skF_2', '#skF_1', E_448, '#skF_4')=k5_relat_1(E_448, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_448, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~v1_funct_1(E_448))), inference(resolution, [status(thm)], [c_60, c_2468])).
% 5.10/1.97  tff(c_2485, plain, (![A_456, B_457, E_458]: (k1_partfun1(A_456, B_457, '#skF_2', '#skF_1', E_458, '#skF_4')=k5_relat_1(E_458, '#skF_4') | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~v1_funct_1(E_458))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2474])).
% 5.10/1.97  tff(c_2491, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2485])).
% 5.10/1.97  tff(c_2498, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2491])).
% 5.10/1.97  tff(c_2230, plain, (![D_398, C_399, A_400, B_401]: (D_398=C_399 | ~r2_relset_1(A_400, B_401, C_399, D_398) | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.10/1.97  tff(c_2238, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2230])).
% 5.10/1.97  tff(c_2253, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2238])).
% 5.10/1.97  tff(c_2389, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2253])).
% 5.10/1.97  tff(c_2503, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_2389])).
% 5.10/1.97  tff(c_2519, plain, (![F_463, C_464, D_459, B_460, A_462, E_461]: (m1_subset_1(k1_partfun1(A_462, B_460, C_464, D_459, E_461, F_463), k1_zfmisc_1(k2_zfmisc_1(A_462, D_459))) | ~m1_subset_1(F_463, k1_zfmisc_1(k2_zfmisc_1(C_464, D_459))) | ~v1_funct_1(F_463) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(A_462, B_460))) | ~v1_funct_1(E_461))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.10/1.97  tff(c_2554, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2498, c_2519])).
% 5.10/1.97  tff(c_2569, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2554])).
% 5.10/1.97  tff(c_2571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2503, c_2569])).
% 5.10/1.97  tff(c_2572, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2253])).
% 5.10/1.97  tff(c_2904, plain, (![A_500, B_501, C_502, D_503]: (k2_relset_1(A_500, B_501, C_502)=B_501 | ~r2_relset_1(B_501, B_501, k1_partfun1(B_501, A_500, A_500, B_501, D_503, C_502), k6_partfun1(B_501)) | ~m1_subset_1(D_503, k1_zfmisc_1(k2_zfmisc_1(B_501, A_500))) | ~v1_funct_2(D_503, B_501, A_500) | ~v1_funct_1(D_503) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_500, B_501))) | ~v1_funct_2(C_502, A_500, B_501) | ~v1_funct_1(C_502))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.10/1.97  tff(c_2910, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2572, c_2904])).
% 5.10/1.97  tff(c_2914, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_2158, c_2175, c_2910])).
% 5.10/1.97  tff(c_38, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.10/1.97  tff(c_2925, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2914, c_38])).
% 5.10/1.97  tff(c_2933, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2025, c_2087, c_2914, c_2925])).
% 5.10/1.97  tff(c_2935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2002, c_2933])).
% 5.10/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.97  
% 5.10/1.97  Inference rules
% 5.10/1.97  ----------------------
% 5.10/1.97  #Ref     : 0
% 5.10/1.97  #Sup     : 587
% 5.10/1.97  #Fact    : 0
% 5.10/1.97  #Define  : 0
% 5.10/1.97  #Split   : 10
% 5.10/1.97  #Chain   : 0
% 5.10/1.97  #Close   : 0
% 5.10/1.97  
% 5.10/1.97  Ordering : KBO
% 5.10/1.97  
% 5.10/1.97  Simplification rules
% 5.10/1.97  ----------------------
% 5.10/1.97  #Subsume      : 43
% 5.10/1.97  #Demod        : 617
% 5.10/1.97  #Tautology    : 163
% 5.10/1.97  #SimpNegUnit  : 6
% 5.10/1.97  #BackRed      : 25
% 5.10/1.97  
% 5.10/1.97  #Partial instantiations: 0
% 5.10/1.97  #Strategies tried      : 1
% 5.10/1.97  
% 5.10/1.97  Timing (in seconds)
% 5.10/1.97  ----------------------
% 5.10/1.97  Preprocessing        : 0.36
% 5.10/1.97  Parsing              : 0.19
% 5.10/1.97  CNF conversion       : 0.02
% 5.10/1.97  Main loop            : 0.82
% 5.10/1.97  Inferencing          : 0.30
% 5.10/1.97  Reduction            : 0.27
% 5.10/1.97  Demodulation         : 0.20
% 5.10/1.97  BG Simplification    : 0.03
% 5.10/1.97  Subsumption          : 0.13
% 5.10/1.97  Abstraction          : 0.04
% 5.10/1.97  MUC search           : 0.00
% 5.10/1.97  Cooper               : 0.00
% 5.10/1.97  Total                : 1.23
% 5.10/1.97  Index Insertion      : 0.00
% 5.10/1.97  Index Deletion       : 0.00
% 5.10/1.97  Index Matching       : 0.00
% 5.10/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
