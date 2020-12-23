%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:16 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 287 expanded)
%              Number of leaves         :   54 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 648 expanded)
%              Number of equality atoms :   52 ( 166 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_144,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E] : ~ v1_xboole_0(k3_enumset1(A,B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_hidden(B,A)
         => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
            & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_108,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_112,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_108])).

tff(c_129,plain,(
    ! [C_108,B_109,A_110] :
      ( v5_relat_1(C_108,B_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_129])).

tff(c_30,plain,(
    ! [B_44,A_43] :
      ( r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v5_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1824,plain,(
    ! [C_363,A_364,B_365] :
      ( r2_hidden(C_363,A_364)
      | ~ r2_hidden(C_363,B_365)
      | ~ m1_subset_1(B_365,k1_zfmisc_1(A_364)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2048,plain,(
    ! [A_412,B_413,A_414] :
      ( r2_hidden('#skF_1'(A_412,B_413),A_414)
      | ~ m1_subset_1(A_412,k1_zfmisc_1(A_414))
      | r1_tarski(A_412,B_413) ) ),
    inference(resolution,[status(thm)],[c_6,c_1824])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2070,plain,(
    ! [A_415,A_416] :
      ( ~ m1_subset_1(A_415,k1_zfmisc_1(A_416))
      | r1_tarski(A_415,A_416) ) ),
    inference(resolution,[status(thm)],[c_2048,c_4])).

tff(c_2074,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_2070])).

tff(c_52,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_2'(A_60),A_60)
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1817,plain,(
    ! [C_360,B_361,A_362] :
      ( r2_hidden(C_360,B_361)
      | ~ r2_hidden(C_360,A_362)
      | ~ r1_tarski(A_362,B_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1823,plain,(
    ! [A_60,B_361] :
      ( r2_hidden('#skF_2'(A_60),B_361)
      | ~ r1_tarski(A_60,B_361)
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_52,c_1817])).

tff(c_10,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2112,plain,(
    ! [A_427,C_428,B_429,D_430] :
      ( k1_mcart_1(A_427) = C_428
      | k1_mcart_1(A_427) = B_429
      | ~ r2_hidden(A_427,k2_zfmisc_1(k2_tarski(B_429,C_428),D_430)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3727,plain,(
    ! [A_599,A_600,D_601] :
      ( k1_mcart_1(A_599) = A_600
      | k1_mcart_1(A_599) = A_600
      | ~ r2_hidden(A_599,k2_zfmisc_1(k1_tarski(A_600),D_601)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2112])).

tff(c_3809,plain,(
    ! [A_603,A_604,D_605] :
      ( k1_mcart_1('#skF_2'(A_603)) = A_604
      | ~ r1_tarski(A_603,k2_zfmisc_1(k1_tarski(A_604),D_605))
      | k1_xboole_0 = A_603 ) ),
    inference(resolution,[status(thm)],[c_1823,c_3727])).

tff(c_3821,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2074,c_3809])).

tff(c_3824,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3821])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3852,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_8])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3853,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_72])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3851,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3824,c_34])).

tff(c_1950,plain,(
    ! [A_397,B_398,C_399] :
      ( k1_relset_1(A_397,B_398,C_399) = k1_relat_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1954,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1950])).

tff(c_3904,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3851,c_1954])).

tff(c_68,plain,(
    ! [B_86,A_85,C_87] :
      ( k1_xboole_0 = B_86
      | k1_relset_1(A_85,B_86,C_87) = A_85
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4286,plain,(
    ! [B_653,A_654,C_655] :
      ( B_653 = '#skF_5'
      | k1_relset_1(A_654,B_653,C_655) = A_654
      | ~ v1_funct_2(C_655,A_654,B_653)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_654,B_653))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_68])).

tff(c_4289,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_4286])).

tff(c_4292,plain,
    ( '#skF_5' = '#skF_4'
    | k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3904,c_4289])).

tff(c_4293,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3853,c_4292])).

tff(c_12,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1897,plain,(
    ! [A_380,B_381,C_382,D_383] : k3_enumset1(A_380,A_380,B_381,C_382,D_383) = k2_enumset1(A_380,B_381,C_382,D_383) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [D_37,A_34,B_35,C_36,E_38] : ~ v1_xboole_0(k3_enumset1(A_34,B_35,C_36,D_37,E_38)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1941,plain,(
    ! [A_388,B_389,C_390,D_391] : ~ v1_xboole_0(k2_enumset1(A_388,B_389,C_390,D_391)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_24])).

tff(c_1944,plain,(
    ! [A_392,B_393,C_394] : ~ v1_xboole_0(k1_enumset1(A_392,B_393,C_394)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1941])).

tff(c_1947,plain,(
    ! [A_395,B_396] : ~ v1_xboole_0(k2_tarski(A_395,B_396)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1944])).

tff(c_1949,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1947])).

tff(c_4306,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4293,c_1949])).

tff(c_4311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_4306])).

tff(c_4313,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3821])).

tff(c_4312,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3821])).

tff(c_56,plain,(
    ! [B_84,A_82] :
      ( r2_hidden(k1_mcart_1(B_84),k1_relat_1(A_82))
      | ~ r2_hidden(B_84,A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4358,plain,(
    ! [A_658] :
      ( r2_hidden('#skF_3',k1_relat_1(A_658))
      | ~ r2_hidden('#skF_2'('#skF_5'),A_658)
      | ~ v1_relat_1(A_658) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4312,c_56])).

tff(c_4374,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_4358])).

tff(c_4387,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_4374])).

tff(c_4388,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4313,c_4387])).

tff(c_2166,plain,(
    ! [B_431,A_432] :
      ( r2_hidden(k1_funct_1(B_431,A_432),k2_relat_1(B_431))
      | ~ r2_hidden(A_432,k1_relat_1(B_431))
      | ~ v1_funct_1(B_431)
      | ~ v1_relat_1(B_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5874,plain,(
    ! [B_824,A_825,B_826] :
      ( r2_hidden(k1_funct_1(B_824,A_825),B_826)
      | ~ r1_tarski(k2_relat_1(B_824),B_826)
      | ~ r2_hidden(A_825,k1_relat_1(B_824))
      | ~ v1_funct_1(B_824)
      | ~ v1_relat_1(B_824) ) ),
    inference(resolution,[status(thm)],[c_2166,c_2])).

tff(c_70,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_5910,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5874,c_70])).

tff(c_5923,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_4388,c_5910])).

tff(c_5926,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_5923])).

tff(c_5930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_133,c_5926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.85/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.37  
% 6.85/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 6.85/2.38  
% 6.85/2.38  %Foreground sorts:
% 6.85/2.38  
% 6.85/2.38  
% 6.85/2.38  %Background operators:
% 6.85/2.38  
% 6.85/2.38  
% 6.85/2.38  %Foreground operators:
% 6.85/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.85/2.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.85/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.85/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.85/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.85/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.85/2.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.85/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.85/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.85/2.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.85/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.85/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.85/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.85/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.85/2.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.85/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.85/2.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.85/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.85/2.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.85/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.85/2.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.85/2.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.85/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.85/2.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.85/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.85/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.85/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.85/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.85/2.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.85/2.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.85/2.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.85/2.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.85/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.85/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.85/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.85/2.38  
% 6.85/2.39  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 6.85/2.39  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.85/2.39  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.85/2.39  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.85/2.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.85/2.39  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.85/2.39  tff(f_117, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 6.85/2.39  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.85/2.39  tff(f_96, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 6.85/2.39  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.85/2.39  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.85/2.39  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.85/2.39  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.85/2.39  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.85/2.39  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.85/2.39  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.85/2.39  tff(f_50, axiom, (![A, B, C, D, E]: ~v1_xboole_0(k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_subset_1)).
% 6.85/2.39  tff(f_126, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 6.85/2.39  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 6.85/2.39  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.85/2.39  tff(c_108, plain, (![C_99, A_100, B_101]: (v1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.85/2.39  tff(c_112, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_108])).
% 6.85/2.39  tff(c_129, plain, (![C_108, B_109, A_110]: (v5_relat_1(C_108, B_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.85/2.39  tff(c_133, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_129])).
% 6.85/2.39  tff(c_30, plain, (![B_44, A_43]: (r1_tarski(k2_relat_1(B_44), A_43) | ~v5_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.85/2.39  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.85/2.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.85/2.39  tff(c_1824, plain, (![C_363, A_364, B_365]: (r2_hidden(C_363, A_364) | ~r2_hidden(C_363, B_365) | ~m1_subset_1(B_365, k1_zfmisc_1(A_364)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.85/2.39  tff(c_2048, plain, (![A_412, B_413, A_414]: (r2_hidden('#skF_1'(A_412, B_413), A_414) | ~m1_subset_1(A_412, k1_zfmisc_1(A_414)) | r1_tarski(A_412, B_413))), inference(resolution, [status(thm)], [c_6, c_1824])).
% 6.85/2.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.85/2.39  tff(c_2070, plain, (![A_415, A_416]: (~m1_subset_1(A_415, k1_zfmisc_1(A_416)) | r1_tarski(A_415, A_416))), inference(resolution, [status(thm)], [c_2048, c_4])).
% 6.85/2.39  tff(c_2074, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_2070])).
% 6.85/2.39  tff(c_52, plain, (![A_60]: (r2_hidden('#skF_2'(A_60), A_60) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.85/2.39  tff(c_1817, plain, (![C_360, B_361, A_362]: (r2_hidden(C_360, B_361) | ~r2_hidden(C_360, A_362) | ~r1_tarski(A_362, B_361))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.85/2.39  tff(c_1823, plain, (![A_60, B_361]: (r2_hidden('#skF_2'(A_60), B_361) | ~r1_tarski(A_60, B_361) | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_52, c_1817])).
% 6.85/2.39  tff(c_10, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.85/2.39  tff(c_2112, plain, (![A_427, C_428, B_429, D_430]: (k1_mcart_1(A_427)=C_428 | k1_mcart_1(A_427)=B_429 | ~r2_hidden(A_427, k2_zfmisc_1(k2_tarski(B_429, C_428), D_430)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.85/2.39  tff(c_3727, plain, (![A_599, A_600, D_601]: (k1_mcart_1(A_599)=A_600 | k1_mcart_1(A_599)=A_600 | ~r2_hidden(A_599, k2_zfmisc_1(k1_tarski(A_600), D_601)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2112])).
% 6.85/2.39  tff(c_3809, plain, (![A_603, A_604, D_605]: (k1_mcart_1('#skF_2'(A_603))=A_604 | ~r1_tarski(A_603, k2_zfmisc_1(k1_tarski(A_604), D_605)) | k1_xboole_0=A_603)), inference(resolution, [status(thm)], [c_1823, c_3727])).
% 6.85/2.39  tff(c_3821, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2074, c_3809])).
% 6.85/2.39  tff(c_3824, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3821])).
% 6.85/2.39  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.85/2.39  tff(c_3852, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_8])).
% 6.85/2.39  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.85/2.39  tff(c_3853, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_72])).
% 6.85/2.39  tff(c_76, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.85/2.39  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.85/2.39  tff(c_3851, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3824, c_34])).
% 6.85/2.39  tff(c_1950, plain, (![A_397, B_398, C_399]: (k1_relset_1(A_397, B_398, C_399)=k1_relat_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.85/2.39  tff(c_1954, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_1950])).
% 6.85/2.39  tff(c_3904, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3851, c_1954])).
% 6.85/2.39  tff(c_68, plain, (![B_86, A_85, C_87]: (k1_xboole_0=B_86 | k1_relset_1(A_85, B_86, C_87)=A_85 | ~v1_funct_2(C_87, A_85, B_86) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.85/2.39  tff(c_4286, plain, (![B_653, A_654, C_655]: (B_653='#skF_5' | k1_relset_1(A_654, B_653, C_655)=A_654 | ~v1_funct_2(C_655, A_654, B_653) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_654, B_653))))), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_68])).
% 6.85/2.39  tff(c_4289, plain, ('#skF_5'='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_74, c_4286])).
% 6.85/2.39  tff(c_4292, plain, ('#skF_5'='#skF_4' | k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3904, c_4289])).
% 6.85/2.39  tff(c_4293, plain, (k1_tarski('#skF_3')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3853, c_4292])).
% 6.85/2.39  tff(c_12, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.85/2.39  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.85/2.39  tff(c_1897, plain, (![A_380, B_381, C_382, D_383]: (k3_enumset1(A_380, A_380, B_381, C_382, D_383)=k2_enumset1(A_380, B_381, C_382, D_383))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.85/2.39  tff(c_24, plain, (![D_37, A_34, B_35, C_36, E_38]: (~v1_xboole_0(k3_enumset1(A_34, B_35, C_36, D_37, E_38)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.85/2.39  tff(c_1941, plain, (![A_388, B_389, C_390, D_391]: (~v1_xboole_0(k2_enumset1(A_388, B_389, C_390, D_391)))), inference(superposition, [status(thm), theory('equality')], [c_1897, c_24])).
% 6.85/2.39  tff(c_1944, plain, (![A_392, B_393, C_394]: (~v1_xboole_0(k1_enumset1(A_392, B_393, C_394)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1941])).
% 6.85/2.39  tff(c_1947, plain, (![A_395, B_396]: (~v1_xboole_0(k2_tarski(A_395, B_396)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1944])).
% 6.85/2.39  tff(c_1949, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1947])).
% 6.85/2.39  tff(c_4306, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4293, c_1949])).
% 6.85/2.39  tff(c_4311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3852, c_4306])).
% 6.85/2.39  tff(c_4313, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3821])).
% 6.85/2.39  tff(c_4312, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_3821])).
% 6.85/2.39  tff(c_56, plain, (![B_84, A_82]: (r2_hidden(k1_mcart_1(B_84), k1_relat_1(A_82)) | ~r2_hidden(B_84, A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.85/2.39  tff(c_4358, plain, (![A_658]: (r2_hidden('#skF_3', k1_relat_1(A_658)) | ~r2_hidden('#skF_2'('#skF_5'), A_658) | ~v1_relat_1(A_658))), inference(superposition, [status(thm), theory('equality')], [c_4312, c_56])).
% 6.85/2.39  tff(c_4374, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_52, c_4358])).
% 6.85/2.39  tff(c_4387, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_4374])).
% 6.85/2.39  tff(c_4388, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_4313, c_4387])).
% 6.85/2.39  tff(c_2166, plain, (![B_431, A_432]: (r2_hidden(k1_funct_1(B_431, A_432), k2_relat_1(B_431)) | ~r2_hidden(A_432, k1_relat_1(B_431)) | ~v1_funct_1(B_431) | ~v1_relat_1(B_431))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.85/2.39  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.85/2.39  tff(c_5874, plain, (![B_824, A_825, B_826]: (r2_hidden(k1_funct_1(B_824, A_825), B_826) | ~r1_tarski(k2_relat_1(B_824), B_826) | ~r2_hidden(A_825, k1_relat_1(B_824)) | ~v1_funct_1(B_824) | ~v1_relat_1(B_824))), inference(resolution, [status(thm)], [c_2166, c_2])).
% 6.85/2.39  tff(c_70, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.85/2.39  tff(c_5910, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5874, c_70])).
% 6.85/2.39  tff(c_5923, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_4388, c_5910])).
% 6.85/2.39  tff(c_5926, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_5923])).
% 6.85/2.39  tff(c_5930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_133, c_5926])).
% 6.85/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.39  
% 6.85/2.39  Inference rules
% 6.85/2.39  ----------------------
% 6.85/2.39  #Ref     : 0
% 6.85/2.39  #Sup     : 1341
% 6.85/2.39  #Fact    : 0
% 6.85/2.39  #Define  : 0
% 6.85/2.39  #Split   : 32
% 6.85/2.39  #Chain   : 0
% 6.85/2.39  #Close   : 0
% 6.85/2.39  
% 6.85/2.39  Ordering : KBO
% 6.85/2.39  
% 6.85/2.39  Simplification rules
% 6.85/2.39  ----------------------
% 6.85/2.39  #Subsume      : 263
% 6.85/2.39  #Demod        : 331
% 6.85/2.39  #Tautology    : 162
% 6.85/2.39  #SimpNegUnit  : 49
% 6.85/2.39  #BackRed      : 99
% 6.85/2.39  
% 6.85/2.39  #Partial instantiations: 0
% 6.85/2.39  #Strategies tried      : 1
% 6.85/2.39  
% 6.85/2.39  Timing (in seconds)
% 6.85/2.39  ----------------------
% 6.85/2.40  Preprocessing        : 0.36
% 6.85/2.40  Parsing              : 0.19
% 6.85/2.40  CNF conversion       : 0.03
% 6.85/2.40  Main loop            : 1.25
% 6.85/2.40  Inferencing          : 0.42
% 6.85/2.40  Reduction            : 0.36
% 6.85/2.40  Demodulation         : 0.23
% 6.85/2.40  BG Simplification    : 0.05
% 6.85/2.40  Subsumption          : 0.30
% 6.85/2.40  Abstraction          : 0.05
% 6.85/2.40  MUC search           : 0.00
% 6.85/2.40  Cooper               : 0.00
% 6.85/2.40  Total                : 1.64
% 6.85/2.40  Index Insertion      : 0.00
% 6.85/2.40  Index Deletion       : 0.00
% 6.85/2.40  Index Matching       : 0.00
% 6.85/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
