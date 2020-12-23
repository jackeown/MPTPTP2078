%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:02 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 336 expanded)
%              Number of leaves         :   48 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 711 expanded)
%              Number of equality atoms :   53 ( 165 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_87,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_40,plain,(
    ! [A_43,B_44] : v1_relat_1(k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_151,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_157,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_151])).

tff(c_164,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_157])).

tff(c_54,plain,(
    ! [B_53,A_52] :
      ( r1_tarski(k7_relat_1(B_53,A_52),B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_201,plain,(
    ! [A_94,B_95] :
      ( v1_relat_1(A_94)
      | ~ v1_relat_1(B_95)
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_30,c_151])).

tff(c_229,plain,(
    ! [B_53,A_52] :
      ( v1_relat_1(k7_relat_1(B_53,A_52))
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_54,c_201])).

tff(c_42,plain,(
    ! [B_46,A_45] :
      ( k2_relat_1(k7_relat_1(B_46,A_45)) = k9_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1786,plain,(
    ! [A_293,B_294] :
      ( r1_tarski(k2_relat_1(A_293),k2_relat_1(B_294))
      | ~ r1_tarski(A_293,B_294)
      | ~ v1_relat_1(B_294)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3417,plain,(
    ! [B_487,A_488,B_489] :
      ( r1_tarski(k9_relat_1(B_487,A_488),k2_relat_1(B_489))
      | ~ r1_tarski(k7_relat_1(B_487,A_488),B_489)
      | ~ v1_relat_1(B_489)
      | ~ v1_relat_1(k7_relat_1(B_487,A_488))
      | ~ v1_relat_1(B_487) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1786])).

tff(c_52,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) != k1_xboole_0
      | k1_xboole_0 = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_173,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_164,c_52])).

tff(c_199,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1862,plain,(
    ! [B_315,A_316] :
      ( k1_tarski(k1_funct_1(B_315,A_316)) = k2_relat_1(B_315)
      | k1_tarski(A_316) != k1_relat_1(B_315)
      | ~ v1_funct_1(B_315)
      | ~ v1_relat_1(B_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1868,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_64])).

tff(c_1886,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_72,c_1868])).

tff(c_1949,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1886])).

tff(c_251,plain,(
    ! [C_104,A_105,B_106] :
      ( v4_relat_1(C_104,A_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_264,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_251])).

tff(c_38,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k1_relat_1(B_42),A_41)
      | ~ v4_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2079,plain,(
    ! [B_346,C_347,A_348] :
      ( k2_tarski(B_346,C_347) = A_348
      | k1_tarski(C_347) = A_348
      | k1_tarski(B_346) = A_348
      | k1_xboole_0 = A_348
      | ~ r1_tarski(A_348,k2_tarski(B_346,C_347)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2103,plain,(
    ! [A_1,A_348] :
      ( k2_tarski(A_1,A_1) = A_348
      | k1_tarski(A_1) = A_348
      | k1_tarski(A_1) = A_348
      | k1_xboole_0 = A_348
      | ~ r1_tarski(A_348,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2079])).

tff(c_2289,plain,(
    ! [A_364,A_365] :
      ( k1_tarski(A_364) = A_365
      | k1_tarski(A_364) = A_365
      | k1_tarski(A_364) = A_365
      | k1_xboole_0 = A_365
      | ~ r1_tarski(A_365,k1_tarski(A_364)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2103])).

tff(c_2314,plain,(
    ! [A_366,B_367] :
      ( k1_tarski(A_366) = k1_relat_1(B_367)
      | k1_relat_1(B_367) = k1_xboole_0
      | ~ v4_relat_1(B_367,k1_tarski(A_366))
      | ~ v1_relat_1(B_367) ) ),
    inference(resolution,[status(thm)],[c_38,c_2289])).

tff(c_2328,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_264,c_2314])).

tff(c_2335,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_2328])).

tff(c_2337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_1949,c_2335])).

tff(c_2339,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1886])).

tff(c_2345,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_68])).

tff(c_62,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2462,plain,(
    ! [D_62] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_62) = k9_relat_1('#skF_4',D_62) ),
    inference(resolution,[status(thm)],[c_2345,c_62])).

tff(c_2338,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1886])).

tff(c_2548,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_2338])).

tff(c_2555,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2462,c_2548])).

tff(c_3424,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3417,c_2555])).

tff(c_3441,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_3424])).

tff(c_3447,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3441])).

tff(c_3450,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_229,c_3447])).

tff(c_3454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_3450])).

tff(c_3455,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3441])).

tff(c_3467,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3455])).

tff(c_3471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_3467])).

tff(c_3472,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_26,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_134,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(A_84,B_85)
      | ~ m1_subset_1(A_84,k1_zfmisc_1(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    ! [A_32] : r1_tarski(k1_xboole_0,A_32) ),
    inference(resolution,[status(thm)],[c_26,c_134])).

tff(c_3475,plain,(
    ! [A_32] : r1_tarski('#skF_4',A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3472,c_142])).

tff(c_44,plain,(
    ! [A_47] : k9_relat_1(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3479,plain,(
    ! [A_47] : k9_relat_1('#skF_4',A_47) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3472,c_3472,c_44])).

tff(c_3478,plain,(
    ! [A_32] : m1_subset_1('#skF_4',k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3472,c_26])).

tff(c_4110,plain,(
    ! [A_593,B_594,C_595,D_596] :
      ( k7_relset_1(A_593,B_594,C_595,D_596) = k9_relat_1(C_595,D_596)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4113,plain,(
    ! [A_593,B_594,D_596] : k7_relset_1(A_593,B_594,'#skF_4',D_596) = k9_relat_1('#skF_4',D_596) ),
    inference(resolution,[status(thm)],[c_3478,c_4110])).

tff(c_4118,plain,(
    ! [A_593,B_594,D_596] : k7_relset_1(A_593,B_594,'#skF_4',D_596) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3479,c_4113])).

tff(c_4120,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4118,c_64])).

tff(c_4123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3475,c_4120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.25  
% 6.28/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.57/2.25  
% 6.57/2.25  %Foreground sorts:
% 6.57/2.25  
% 6.57/2.25  
% 6.57/2.25  %Background operators:
% 6.57/2.25  
% 6.57/2.25  
% 6.57/2.25  %Foreground operators:
% 6.57/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.57/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.57/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.57/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.57/2.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.57/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.57/2.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.57/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.57/2.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.57/2.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.57/2.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.57/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.57/2.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.57/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.57/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.57/2.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.57/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.57/2.25  tff('#skF_1', type, '#skF_1': $i).
% 6.57/2.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.57/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.57/2.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.57/2.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.57/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.57/2.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.57/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.57/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.57/2.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.57/2.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.57/2.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.57/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.57/2.25  
% 6.70/2.28  tff(f_81, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.70/2.28  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 6.70/2.28  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.70/2.28  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.70/2.28  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.70/2.28  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.70/2.28  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 6.70/2.28  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.70/2.28  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 6.70/2.28  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.70/2.28  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.70/2.28  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.70/2.28  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 6.70/2.28  tff(f_128, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.70/2.28  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.70/2.28  tff(f_87, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 6.70/2.28  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.70/2.28  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.70/2.28  tff(c_151, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.70/2.28  tff(c_157, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_151])).
% 6.70/2.28  tff(c_164, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_157])).
% 6.70/2.28  tff(c_54, plain, (![B_53, A_52]: (r1_tarski(k7_relat_1(B_53, A_52), B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.70/2.28  tff(c_30, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.70/2.28  tff(c_201, plain, (![A_94, B_95]: (v1_relat_1(A_94) | ~v1_relat_1(B_95) | ~r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_30, c_151])).
% 6.70/2.28  tff(c_229, plain, (![B_53, A_52]: (v1_relat_1(k7_relat_1(B_53, A_52)) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_54, c_201])).
% 6.70/2.28  tff(c_42, plain, (![B_46, A_45]: (k2_relat_1(k7_relat_1(B_46, A_45))=k9_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.70/2.28  tff(c_1786, plain, (![A_293, B_294]: (r1_tarski(k2_relat_1(A_293), k2_relat_1(B_294)) | ~r1_tarski(A_293, B_294) | ~v1_relat_1(B_294) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.70/2.28  tff(c_3417, plain, (![B_487, A_488, B_489]: (r1_tarski(k9_relat_1(B_487, A_488), k2_relat_1(B_489)) | ~r1_tarski(k7_relat_1(B_487, A_488), B_489) | ~v1_relat_1(B_489) | ~v1_relat_1(k7_relat_1(B_487, A_488)) | ~v1_relat_1(B_487))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1786])).
% 6.70/2.28  tff(c_52, plain, (![A_51]: (k1_relat_1(A_51)!=k1_xboole_0 | k1_xboole_0=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.70/2.28  tff(c_173, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_164, c_52])).
% 6.70/2.28  tff(c_199, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_173])).
% 6.70/2.28  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.70/2.28  tff(c_1862, plain, (![B_315, A_316]: (k1_tarski(k1_funct_1(B_315, A_316))=k2_relat_1(B_315) | k1_tarski(A_316)!=k1_relat_1(B_315) | ~v1_funct_1(B_315) | ~v1_relat_1(B_315))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.70/2.28  tff(c_64, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.70/2.28  tff(c_1868, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1862, c_64])).
% 6.70/2.28  tff(c_1886, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_72, c_1868])).
% 6.70/2.28  tff(c_1949, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1886])).
% 6.70/2.28  tff(c_251, plain, (![C_104, A_105, B_106]: (v4_relat_1(C_104, A_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.70/2.28  tff(c_264, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_251])).
% 6.70/2.28  tff(c_38, plain, (![B_42, A_41]: (r1_tarski(k1_relat_1(B_42), A_41) | ~v4_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.70/2.28  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.70/2.28  tff(c_2079, plain, (![B_346, C_347, A_348]: (k2_tarski(B_346, C_347)=A_348 | k1_tarski(C_347)=A_348 | k1_tarski(B_346)=A_348 | k1_xboole_0=A_348 | ~r1_tarski(A_348, k2_tarski(B_346, C_347)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.70/2.28  tff(c_2103, plain, (![A_1, A_348]: (k2_tarski(A_1, A_1)=A_348 | k1_tarski(A_1)=A_348 | k1_tarski(A_1)=A_348 | k1_xboole_0=A_348 | ~r1_tarski(A_348, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2079])).
% 6.70/2.28  tff(c_2289, plain, (![A_364, A_365]: (k1_tarski(A_364)=A_365 | k1_tarski(A_364)=A_365 | k1_tarski(A_364)=A_365 | k1_xboole_0=A_365 | ~r1_tarski(A_365, k1_tarski(A_364)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2103])).
% 6.70/2.28  tff(c_2314, plain, (![A_366, B_367]: (k1_tarski(A_366)=k1_relat_1(B_367) | k1_relat_1(B_367)=k1_xboole_0 | ~v4_relat_1(B_367, k1_tarski(A_366)) | ~v1_relat_1(B_367))), inference(resolution, [status(thm)], [c_38, c_2289])).
% 6.70/2.28  tff(c_2328, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_264, c_2314])).
% 6.70/2.28  tff(c_2335, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_164, c_2328])).
% 6.70/2.28  tff(c_2337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_1949, c_2335])).
% 6.70/2.28  tff(c_2339, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1886])).
% 6.70/2.28  tff(c_2345, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2339, c_68])).
% 6.70/2.28  tff(c_62, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.70/2.28  tff(c_2462, plain, (![D_62]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_62)=k9_relat_1('#skF_4', D_62))), inference(resolution, [status(thm)], [c_2345, c_62])).
% 6.70/2.28  tff(c_2338, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1886])).
% 6.70/2.28  tff(c_2548, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2339, c_2338])).
% 6.70/2.28  tff(c_2555, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2462, c_2548])).
% 6.70/2.28  tff(c_3424, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3417, c_2555])).
% 6.70/2.28  tff(c_3441, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_3424])).
% 6.70/2.28  tff(c_3447, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3441])).
% 6.70/2.28  tff(c_3450, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_229, c_3447])).
% 6.70/2.28  tff(c_3454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_3450])).
% 6.70/2.28  tff(c_3455, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_3441])).
% 6.70/2.28  tff(c_3467, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3455])).
% 6.70/2.28  tff(c_3471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_3467])).
% 6.70/2.28  tff(c_3472, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_173])).
% 6.70/2.28  tff(c_26, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.70/2.28  tff(c_134, plain, (![A_84, B_85]: (r1_tarski(A_84, B_85) | ~m1_subset_1(A_84, k1_zfmisc_1(B_85)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.70/2.28  tff(c_142, plain, (![A_32]: (r1_tarski(k1_xboole_0, A_32))), inference(resolution, [status(thm)], [c_26, c_134])).
% 6.70/2.28  tff(c_3475, plain, (![A_32]: (r1_tarski('#skF_4', A_32))), inference(demodulation, [status(thm), theory('equality')], [c_3472, c_142])).
% 6.70/2.28  tff(c_44, plain, (![A_47]: (k9_relat_1(k1_xboole_0, A_47)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.70/2.28  tff(c_3479, plain, (![A_47]: (k9_relat_1('#skF_4', A_47)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3472, c_3472, c_44])).
% 6.70/2.28  tff(c_3478, plain, (![A_32]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_3472, c_26])).
% 6.70/2.28  tff(c_4110, plain, (![A_593, B_594, C_595, D_596]: (k7_relset_1(A_593, B_594, C_595, D_596)=k9_relat_1(C_595, D_596) | ~m1_subset_1(C_595, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.70/2.28  tff(c_4113, plain, (![A_593, B_594, D_596]: (k7_relset_1(A_593, B_594, '#skF_4', D_596)=k9_relat_1('#skF_4', D_596))), inference(resolution, [status(thm)], [c_3478, c_4110])).
% 6.70/2.28  tff(c_4118, plain, (![A_593, B_594, D_596]: (k7_relset_1(A_593, B_594, '#skF_4', D_596)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3479, c_4113])).
% 6.70/2.28  tff(c_4120, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4118, c_64])).
% 6.70/2.28  tff(c_4123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3475, c_4120])).
% 6.70/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.70/2.28  
% 6.70/2.28  Inference rules
% 6.70/2.28  ----------------------
% 6.70/2.28  #Ref     : 0
% 6.70/2.28  #Sup     : 832
% 6.70/2.28  #Fact    : 1
% 6.70/2.28  #Define  : 0
% 6.70/2.28  #Split   : 18
% 6.70/2.28  #Chain   : 0
% 6.70/2.28  #Close   : 0
% 6.70/2.28  
% 6.70/2.28  Ordering : KBO
% 6.70/2.28  
% 6.70/2.28  Simplification rules
% 6.70/2.28  ----------------------
% 6.70/2.28  #Subsume      : 163
% 6.70/2.28  #Demod        : 755
% 6.70/2.28  #Tautology    : 302
% 6.70/2.28  #SimpNegUnit  : 84
% 6.70/2.28  #BackRed      : 87
% 6.70/2.28  
% 6.70/2.28  #Partial instantiations: 0
% 6.70/2.28  #Strategies tried      : 1
% 6.70/2.28  
% 6.70/2.28  Timing (in seconds)
% 6.70/2.28  ----------------------
% 6.70/2.29  Preprocessing        : 0.36
% 6.70/2.29  Parsing              : 0.19
% 6.70/2.29  CNF conversion       : 0.03
% 6.70/2.29  Main loop            : 1.11
% 6.70/2.29  Inferencing          : 0.38
% 6.70/2.29  Reduction            : 0.38
% 6.70/2.29  Demodulation         : 0.27
% 6.70/2.29  BG Simplification    : 0.04
% 6.70/2.29  Subsumption          : 0.22
% 6.70/2.29  Abstraction          : 0.05
% 6.70/2.29  MUC search           : 0.00
% 6.70/2.29  Cooper               : 0.00
% 6.70/2.29  Total                : 1.54
% 6.70/2.29  Index Insertion      : 0.00
% 6.70/2.29  Index Deletion       : 0.00
% 6.70/2.29  Index Matching       : 0.00
% 6.70/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
