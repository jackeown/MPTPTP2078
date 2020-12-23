%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 852 expanded)
%              Number of leaves         :   46 ( 282 expanded)
%              Depth                    :   12
%              Number of atoms          :  266 (2723 expanded)
%              Number of equality atoms :   95 ( 506 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_142,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_156,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_70,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_807,plain,(
    ! [B_146,A_147] :
      ( v1_relat_1(B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_147))
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_810,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_807])).

tff(c_816,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_810])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2894,plain,(
    ! [A_360,B_361,C_362] :
      ( k1_relset_1(A_360,B_361,C_362) = k1_relat_1(C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2912,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2894])).

tff(c_3760,plain,(
    ! [B_492,A_493,C_494] :
      ( k1_xboole_0 = B_492
      | k1_relset_1(A_493,B_492,C_494) = A_493
      | ~ v1_funct_2(C_494,A_493,B_492)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(A_493,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3769,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_3760])).

tff(c_3784,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2912,c_3769])).

tff(c_3788,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3784])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(k7_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3799,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3788,c_34])).

tff(c_3807,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_3799])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3546,plain,(
    ! [A_478,B_479,C_480,D_481] :
      ( k2_partfun1(A_478,B_479,C_480,D_481) = k7_relat_1(C_480,D_481)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_478,B_479)))
      | ~ v1_funct_1(C_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3552,plain,(
    ! [D_481] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_481) = k7_relat_1('#skF_5',D_481)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_3546])).

tff(c_3566,plain,(
    ! [D_481] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_481) = k7_relat_1('#skF_5',D_481) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3552])).

tff(c_1073,plain,(
    ! [A_177,B_178,C_179] :
      ( k1_relset_1(A_177,B_178,C_179) = k1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1087,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_1073])).

tff(c_2065,plain,(
    ! [B_304,A_305,C_306] :
      ( k1_xboole_0 = B_304
      | k1_relset_1(A_305,B_304,C_306) = A_305
      | ~ v1_funct_2(C_306,A_305,B_304)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2071,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2065])).

tff(c_2085,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1087,c_2071])).

tff(c_2093,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2085])).

tff(c_2106,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_34])).

tff(c_2122,plain,(
    ! [A_308] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_308)) = A_308
      | ~ r1_tarski(A_308,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_2106])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2155,plain,(
    ! [A_308] :
      ( r1_tarski(A_308,A_308)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_308,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2122,c_32])).

tff(c_2183,plain,(
    ! [A_309] :
      ( r1_tarski(A_309,A_309)
      | ~ r1_tarski(A_309,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_2155])).

tff(c_2194,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_2183])).

tff(c_2116,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_2106])).

tff(c_1512,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k7_relset_1(A_241,B_242,C_243,D_244) = k9_relat_1(C_243,D_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1522,plain,(
    ! [D_244] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_244) = k9_relat_1('#skF_5',D_244) ),
    inference(resolution,[status(thm)],[c_72,c_1512])).

tff(c_68,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1524,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_68])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1919,plain,(
    ! [A_295,B_296,C_297,D_298] :
      ( k2_partfun1(A_295,B_296,C_297,D_298) = k7_relat_1(C_297,D_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ v1_funct_1(C_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1923,plain,(
    ! [D_298] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_298) = k7_relat_1('#skF_5',D_298)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_1919])).

tff(c_1934,plain,(
    ! [D_298] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_298) = k7_relat_1('#skF_5',D_298) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1923])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1749,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k2_partfun1(A_283,B_284,C_285,D_286) = k7_relat_1(C_285,D_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1753,plain,(
    ! [D_286] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_286) = k7_relat_1('#skF_5',D_286)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_1749])).

tff(c_1764,plain,(
    ! [D_286] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_286) = k7_relat_1('#skF_5',D_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1753])).

tff(c_1603,plain,(
    ! [C_265,A_266,B_267] :
      ( m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267)))
      | ~ r1_tarski(k2_relat_1(C_265),B_267)
      | ~ r1_tarski(k1_relat_1(C_265),A_266)
      | ~ v1_relat_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_788,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( v1_funct_1(k2_partfun1(A_142,B_143,C_144,D_145))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_790,plain,(
    ! [D_145] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_145))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_788])).

tff(c_800,plain,(
    ! [D_145] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_145)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_790])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_156,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_156])).

tff(c_805,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_819,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_805])).

tff(c_1637,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1603,c_819])).

tff(c_1675,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1637])).

tff(c_1768,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1675])).

tff(c_1786,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1768])).

tff(c_1790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_1786])).

tff(c_1791,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1637])).

tff(c_2270,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_1934,c_1791])).

tff(c_2271,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2270])).

tff(c_2274,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2271])).

tff(c_2280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_1524,c_2274])).

tff(c_2281,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2270])).

tff(c_2302,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_2281])).

tff(c_2308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2194,c_2302])).

tff(c_2309,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2085])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2369,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2309,c_2])).

tff(c_2371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2369])).

tff(c_2373,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_805])).

tff(c_2911,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2373,c_2894])).

tff(c_3574,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_3566,c_2911])).

tff(c_2372,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_805])).

tff(c_3580,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_2372])).

tff(c_3579,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_2373])).

tff(c_54,plain,(
    ! [B_44,C_45,A_43] :
      ( k1_xboole_0 = B_44
      | v1_funct_2(C_45,A_43,B_44)
      | k1_relset_1(A_43,B_44,C_45) != A_43
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3701,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3579,c_54])).

tff(c_3724,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3580,c_3701])).

tff(c_3813,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3724])).

tff(c_4299,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3574,c_3813])).

tff(c_4306,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3807,c_4299])).

tff(c_4310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4306])).

tff(c_4311,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3724])).

tff(c_116,plain,(
    ! [A_64] :
      ( k7_relat_1(A_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_128,plain,(
    ! [A_15,B_16] : k7_relat_1(k2_zfmisc_1(A_15,B_16),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_2374,plain,(
    ! [B_319,A_320] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_319,A_320)),A_320)
      | ~ v1_relat_1(B_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2381,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2374])).

tff(c_2387,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2381])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2397,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2387,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2904,plain,(
    ! [A_360,B_361] : k1_relset_1(A_360,B_361,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_2894])).

tff(c_2914,plain,(
    ! [A_360,B_361] : k1_relset_1(A_360,B_361,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2397,c_2904])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [C_45,B_44] :
      ( v1_funct_2(C_45,k1_xboole_0,B_44)
      | k1_relset_1(k1_xboole_0,B_44,C_45) != k1_xboole_0
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2939,plain,(
    ! [C_370,B_371] :
      ( v1_funct_2(C_370,k1_xboole_0,B_371)
      | k1_relset_1(k1_xboole_0,B_371,C_370) != k1_xboole_0
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_2942,plain,(
    ! [B_371] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_371)
      | k1_relset_1(k1_xboole_0,B_371,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_2939])).

tff(c_2945,plain,(
    ! [B_371] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_371) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2914,c_2942])).

tff(c_4332,plain,(
    ! [B_371] : v1_funct_2('#skF_3','#skF_3',B_371) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4311,c_4311,c_2945])).

tff(c_26,plain,(
    ! [A_17] :
      ( k7_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2393,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_816,c_26])).

tff(c_4358,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4311,c_4311,c_2393])).

tff(c_3363,plain,(
    ! [A_445,B_446,C_447,D_448] :
      ( k7_relset_1(A_445,B_446,C_447,D_448) = k9_relat_1(C_447,D_448)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3376,plain,(
    ! [D_448] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_448) = k9_relat_1('#skF_5',D_448) ),
    inference(resolution,[status(thm)],[c_72,c_3363])).

tff(c_3378,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_68])).

tff(c_4587,plain,(
    ! [A_528] :
      ( A_528 = '#skF_3'
      | ~ r1_tarski(A_528,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4311,c_4311,c_4])).

tff(c_4604,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3378,c_4587])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(B_21,A_20) != k1_xboole_0
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3796,plain,(
    ! [A_20] :
      ( k9_relat_1('#skF_5',A_20) != k1_xboole_0
      | ~ r1_tarski(A_20,'#skF_1')
      | k1_xboole_0 = A_20
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3788,c_30])).

tff(c_3805,plain,(
    ! [A_20] :
      ( k9_relat_1('#skF_5',A_20) != k1_xboole_0
      | ~ r1_tarski(A_20,'#skF_1')
      | k1_xboole_0 = A_20 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_3796])).

tff(c_5379,plain,(
    ! [A_598] :
      ( k9_relat_1('#skF_5',A_598) != '#skF_3'
      | ~ r1_tarski(A_598,'#skF_1')
      | A_598 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4311,c_4311,c_3805])).

tff(c_5390,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_70,c_5379])).

tff(c_5395,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4604,c_5390])).

tff(c_5409,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5395,c_5395,c_3580])).

tff(c_5427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4332,c_4358,c_5409])).

tff(c_5428,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3784])).

tff(c_5487,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5428,c_2])).

tff(c_5489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.22  
% 6.28/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.22  %$ v1_funct_2 > v5_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.28/2.22  
% 6.28/2.22  %Foreground sorts:
% 6.28/2.22  
% 6.28/2.22  
% 6.28/2.22  %Background operators:
% 6.28/2.22  
% 6.28/2.22  
% 6.28/2.22  %Foreground operators:
% 6.28/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.28/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.28/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.28/2.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.28/2.22  tff('#skF_5', type, '#skF_5': $i).
% 6.28/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.28/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.28/2.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.28/2.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.28/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.28/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.28/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.28/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.28/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.28/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.28/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.28/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.28/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.23  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.28/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.28/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.28/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.28/2.23  
% 6.28/2.26  tff(f_177, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 6.28/2.26  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.28/2.26  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.28/2.26  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.28/2.26  tff(f_142, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.28/2.26  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 6.28/2.26  tff(f_156, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.28/2.26  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 6.28/2.26  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.28/2.26  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.28/2.26  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.28/2.26  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 6.28/2.26  tff(f_150, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.28/2.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.28/2.26  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 6.28/2.26  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.28/2.26  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.28/2.26  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.28/2.26  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 6.28/2.26  tff(c_78, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_70, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.28/2.26  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_807, plain, (![B_146, A_147]: (v1_relat_1(B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(A_147)) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.28/2.26  tff(c_810, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_807])).
% 6.28/2.26  tff(c_816, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_810])).
% 6.28/2.26  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_2894, plain, (![A_360, B_361, C_362]: (k1_relset_1(A_360, B_361, C_362)=k1_relat_1(C_362) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.28/2.26  tff(c_2912, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2894])).
% 6.28/2.26  tff(c_3760, plain, (![B_492, A_493, C_494]: (k1_xboole_0=B_492 | k1_relset_1(A_493, B_492, C_494)=A_493 | ~v1_funct_2(C_494, A_493, B_492) | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(A_493, B_492))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.28/2.26  tff(c_3769, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_3760])).
% 6.28/2.26  tff(c_3784, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2912, c_3769])).
% 6.28/2.26  tff(c_3788, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_3784])).
% 6.28/2.26  tff(c_34, plain, (![B_25, A_24]: (k1_relat_1(k7_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.28/2.26  tff(c_3799, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3788, c_34])).
% 6.28/2.26  tff(c_3807, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_3799])).
% 6.28/2.26  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_3546, plain, (![A_478, B_479, C_480, D_481]: (k2_partfun1(A_478, B_479, C_480, D_481)=k7_relat_1(C_480, D_481) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(A_478, B_479))) | ~v1_funct_1(C_480))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.28/2.26  tff(c_3552, plain, (![D_481]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_481)=k7_relat_1('#skF_5', D_481) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_3546])).
% 6.28/2.26  tff(c_3566, plain, (![D_481]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_481)=k7_relat_1('#skF_5', D_481))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3552])).
% 6.28/2.26  tff(c_1073, plain, (![A_177, B_178, C_179]: (k1_relset_1(A_177, B_178, C_179)=k1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.28/2.26  tff(c_1087, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_1073])).
% 6.28/2.26  tff(c_2065, plain, (![B_304, A_305, C_306]: (k1_xboole_0=B_304 | k1_relset_1(A_305, B_304, C_306)=A_305 | ~v1_funct_2(C_306, A_305, B_304) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.28/2.26  tff(c_2071, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_2065])).
% 6.28/2.26  tff(c_2085, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1087, c_2071])).
% 6.28/2.26  tff(c_2093, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_2085])).
% 6.28/2.26  tff(c_2106, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_34])).
% 6.28/2.26  tff(c_2122, plain, (![A_308]: (k1_relat_1(k7_relat_1('#skF_5', A_308))=A_308 | ~r1_tarski(A_308, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_2106])).
% 6.28/2.26  tff(c_32, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.28/2.26  tff(c_2155, plain, (![A_308]: (r1_tarski(A_308, A_308) | ~v1_relat_1('#skF_5') | ~r1_tarski(A_308, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2122, c_32])).
% 6.28/2.26  tff(c_2183, plain, (![A_309]: (r1_tarski(A_309, A_309) | ~r1_tarski(A_309, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_2155])).
% 6.28/2.26  tff(c_2194, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_2183])).
% 6.28/2.26  tff(c_2116, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_2106])).
% 6.28/2.26  tff(c_1512, plain, (![A_241, B_242, C_243, D_244]: (k7_relset_1(A_241, B_242, C_243, D_244)=k9_relat_1(C_243, D_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.28/2.26  tff(c_1522, plain, (![D_244]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_244)=k9_relat_1('#skF_5', D_244))), inference(resolution, [status(thm)], [c_72, c_1512])).
% 6.28/2.26  tff(c_68, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_1524, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_68])).
% 6.28/2.26  tff(c_28, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.28/2.26  tff(c_1919, plain, (![A_295, B_296, C_297, D_298]: (k2_partfun1(A_295, B_296, C_297, D_298)=k7_relat_1(C_297, D_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~v1_funct_1(C_297))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.28/2.26  tff(c_1923, plain, (![D_298]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_298)=k7_relat_1('#skF_5', D_298) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_1919])).
% 6.28/2.26  tff(c_1934, plain, (![D_298]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_298)=k7_relat_1('#skF_5', D_298))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1923])).
% 6.28/2.26  tff(c_22, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.28/2.26  tff(c_1749, plain, (![A_283, B_284, C_285, D_286]: (k2_partfun1(A_283, B_284, C_285, D_286)=k7_relat_1(C_285, D_286) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.28/2.26  tff(c_1753, plain, (![D_286]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_286)=k7_relat_1('#skF_5', D_286) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_1749])).
% 6.28/2.26  tff(c_1764, plain, (![D_286]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_286)=k7_relat_1('#skF_5', D_286))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1753])).
% 6.28/2.26  tff(c_1603, plain, (![C_265, A_266, B_267]: (m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))) | ~r1_tarski(k2_relat_1(C_265), B_267) | ~r1_tarski(k1_relat_1(C_265), A_266) | ~v1_relat_1(C_265))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.28/2.26  tff(c_788, plain, (![A_142, B_143, C_144, D_145]: (v1_funct_1(k2_partfun1(A_142, B_143, C_144, D_145)) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.28/2.26  tff(c_790, plain, (![D_145]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_145)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_788])).
% 6.28/2.26  tff(c_800, plain, (![D_145]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_145)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_790])).
% 6.28/2.26  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.28/2.26  tff(c_156, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_66])).
% 6.28/2.26  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_800, c_156])).
% 6.28/2.26  tff(c_805, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 6.28/2.26  tff(c_819, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_805])).
% 6.28/2.26  tff(c_1637, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_1603, c_819])).
% 6.28/2.26  tff(c_1675, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1637])).
% 6.28/2.26  tff(c_1768, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1675])).
% 6.28/2.26  tff(c_1786, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1768])).
% 6.28/2.26  tff(c_1790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_816, c_1786])).
% 6.28/2.26  tff(c_1791, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_1637])).
% 6.28/2.26  tff(c_2270, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1934, c_1934, c_1791])).
% 6.28/2.26  tff(c_2271, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_2270])).
% 6.28/2.26  tff(c_2274, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2271])).
% 6.28/2.26  tff(c_2280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_816, c_1524, c_2274])).
% 6.28/2.26  tff(c_2281, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_2270])).
% 6.28/2.26  tff(c_2302, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2116, c_2281])).
% 6.28/2.26  tff(c_2308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2194, c_2302])).
% 6.28/2.26  tff(c_2309, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2085])).
% 6.28/2.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.28/2.26  tff(c_2369, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2309, c_2])).
% 6.28/2.26  tff(c_2371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2369])).
% 6.28/2.26  tff(c_2373, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_805])).
% 6.28/2.26  tff(c_2911, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_2373, c_2894])).
% 6.28/2.26  tff(c_3574, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_3566, c_2911])).
% 6.28/2.26  tff(c_2372, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_805])).
% 6.28/2.26  tff(c_3580, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_2372])).
% 6.28/2.26  tff(c_3579, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_2373])).
% 6.28/2.26  tff(c_54, plain, (![B_44, C_45, A_43]: (k1_xboole_0=B_44 | v1_funct_2(C_45, A_43, B_44) | k1_relset_1(A_43, B_44, C_45)!=A_43 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.28/2.26  tff(c_3701, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_3579, c_54])).
% 6.28/2.26  tff(c_3724, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3580, c_3701])).
% 6.28/2.26  tff(c_3813, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3724])).
% 6.28/2.26  tff(c_4299, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3574, c_3813])).
% 6.28/2.26  tff(c_4306, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3807, c_4299])).
% 6.28/2.26  tff(c_4310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_4306])).
% 6.28/2.26  tff(c_4311, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3724])).
% 6.28/2.26  tff(c_116, plain, (![A_64]: (k7_relat_1(A_64, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.28/2.26  tff(c_128, plain, (![A_15, B_16]: (k7_relat_1(k2_zfmisc_1(A_15, B_16), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_116])).
% 6.28/2.26  tff(c_2374, plain, (![B_319, A_320]: (r1_tarski(k1_relat_1(k7_relat_1(B_319, A_320)), A_320) | ~v1_relat_1(B_319))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.28/2.26  tff(c_2381, plain, (![A_15, B_16]: (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2374])).
% 6.28/2.26  tff(c_2387, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2381])).
% 6.28/2.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.28/2.26  tff(c_2397, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2387, c_4])).
% 6.28/2.26  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.28/2.26  tff(c_2904, plain, (![A_360, B_361]: (k1_relset_1(A_360, B_361, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_2894])).
% 6.28/2.26  tff(c_2914, plain, (![A_360, B_361]: (k1_relset_1(A_360, B_361, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2397, c_2904])).
% 6.28/2.26  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.28/2.26  tff(c_52, plain, (![C_45, B_44]: (v1_funct_2(C_45, k1_xboole_0, B_44) | k1_relset_1(k1_xboole_0, B_44, C_45)!=k1_xboole_0 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_44))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.28/2.26  tff(c_2939, plain, (![C_370, B_371]: (v1_funct_2(C_370, k1_xboole_0, B_371) | k1_relset_1(k1_xboole_0, B_371, C_370)!=k1_xboole_0 | ~m1_subset_1(C_370, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 6.28/2.26  tff(c_2942, plain, (![B_371]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_371) | k1_relset_1(k1_xboole_0, B_371, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_2939])).
% 6.28/2.26  tff(c_2945, plain, (![B_371]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_371))), inference(demodulation, [status(thm), theory('equality')], [c_2914, c_2942])).
% 6.28/2.26  tff(c_4332, plain, (![B_371]: (v1_funct_2('#skF_3', '#skF_3', B_371))), inference(demodulation, [status(thm), theory('equality')], [c_4311, c_4311, c_2945])).
% 6.28/2.26  tff(c_26, plain, (![A_17]: (k7_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.28/2.26  tff(c_2393, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_816, c_26])).
% 6.28/2.26  tff(c_4358, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4311, c_4311, c_2393])).
% 6.28/2.26  tff(c_3363, plain, (![A_445, B_446, C_447, D_448]: (k7_relset_1(A_445, B_446, C_447, D_448)=k9_relat_1(C_447, D_448) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.28/2.26  tff(c_3376, plain, (![D_448]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_448)=k9_relat_1('#skF_5', D_448))), inference(resolution, [status(thm)], [c_72, c_3363])).
% 6.28/2.26  tff(c_3378, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_68])).
% 6.28/2.26  tff(c_4587, plain, (![A_528]: (A_528='#skF_3' | ~r1_tarski(A_528, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4311, c_4311, c_4])).
% 6.28/2.26  tff(c_4604, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_3378, c_4587])).
% 6.28/2.26  tff(c_30, plain, (![B_21, A_20]: (k9_relat_1(B_21, A_20)!=k1_xboole_0 | ~r1_tarski(A_20, k1_relat_1(B_21)) | k1_xboole_0=A_20 | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.28/2.26  tff(c_3796, plain, (![A_20]: (k9_relat_1('#skF_5', A_20)!=k1_xboole_0 | ~r1_tarski(A_20, '#skF_1') | k1_xboole_0=A_20 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3788, c_30])).
% 6.28/2.26  tff(c_3805, plain, (![A_20]: (k9_relat_1('#skF_5', A_20)!=k1_xboole_0 | ~r1_tarski(A_20, '#skF_1') | k1_xboole_0=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_816, c_3796])).
% 6.28/2.26  tff(c_5379, plain, (![A_598]: (k9_relat_1('#skF_5', A_598)!='#skF_3' | ~r1_tarski(A_598, '#skF_1') | A_598='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4311, c_4311, c_3805])).
% 6.28/2.26  tff(c_5390, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_70, c_5379])).
% 6.28/2.26  tff(c_5395, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4604, c_5390])).
% 6.28/2.26  tff(c_5409, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5395, c_5395, c_3580])).
% 6.28/2.26  tff(c_5427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4332, c_4358, c_5409])).
% 6.28/2.26  tff(c_5428, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3784])).
% 6.28/2.26  tff(c_5487, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5428, c_2])).
% 6.28/2.26  tff(c_5489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5487])).
% 6.28/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.26  
% 6.28/2.26  Inference rules
% 6.28/2.26  ----------------------
% 6.28/2.26  #Ref     : 0
% 6.28/2.26  #Sup     : 1158
% 6.28/2.26  #Fact    : 0
% 6.28/2.26  #Define  : 0
% 6.28/2.26  #Split   : 15
% 6.28/2.26  #Chain   : 0
% 6.28/2.26  #Close   : 0
% 6.28/2.26  
% 6.28/2.26  Ordering : KBO
% 6.28/2.26  
% 6.28/2.26  Simplification rules
% 6.28/2.26  ----------------------
% 6.28/2.26  #Subsume      : 63
% 6.28/2.26  #Demod        : 1533
% 6.28/2.26  #Tautology    : 664
% 6.28/2.26  #SimpNegUnit  : 9
% 6.28/2.26  #BackRed      : 243
% 6.28/2.26  
% 6.28/2.26  #Partial instantiations: 0
% 6.28/2.26  #Strategies tried      : 1
% 6.28/2.26  
% 6.28/2.26  Timing (in seconds)
% 6.28/2.26  ----------------------
% 6.28/2.26  Preprocessing        : 0.36
% 6.28/2.26  Parsing              : 0.20
% 6.28/2.26  CNF conversion       : 0.02
% 6.28/2.26  Main loop            : 1.09
% 6.28/2.27  Inferencing          : 0.37
% 6.28/2.27  Reduction            : 0.41
% 6.28/2.27  Demodulation         : 0.30
% 6.28/2.27  BG Simplification    : 0.04
% 6.28/2.27  Subsumption          : 0.18
% 6.28/2.27  Abstraction          : 0.05
% 6.28/2.27  MUC search           : 0.00
% 6.28/2.27  Cooper               : 0.00
% 6.28/2.27  Total                : 1.54
% 6.28/2.27  Index Insertion      : 0.00
% 6.28/2.27  Index Deletion       : 0.00
% 6.28/2.27  Index Matching       : 0.00
% 6.28/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
