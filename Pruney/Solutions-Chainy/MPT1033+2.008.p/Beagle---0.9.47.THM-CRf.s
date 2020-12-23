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
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 410 expanded)
%              Number of leaves         :   34 ( 142 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 (1381 expanded)
%              Number of equality atoms :   27 ( 410 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_534,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( r2_relset_1(A_124,B_125,C_126,C_126)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_632,plain,(
    ! [C_128] :
      ( r2_relset_1('#skF_2','#skF_3',C_128,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_66,c_534])).

tff(c_641,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_632])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_381,plain,(
    ! [C_116,A_117,B_118] :
      ( v1_partfun1(C_116,A_117)
      | ~ v1_funct_2(C_116,A_117,B_118)
      | ~ v1_funct_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | v1_xboole_0(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_387,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_381])).

tff(c_404,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_387])).

tff(c_410,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_415,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_410,c_4])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_415])).

tff(c_422,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_390,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_381])).

tff(c_407,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_390])).

tff(c_423,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_407])).

tff(c_421,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_64,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_644,plain,(
    ! [D_129,C_130,A_131,B_132] :
      ( D_129 = C_130
      | ~ r1_partfun1(C_130,D_129)
      | ~ v1_partfun1(D_129,A_131)
      | ~ v1_partfun1(C_130,A_131)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(D_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_646,plain,(
    ! [A_131,B_132] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_131)
      | ~ v1_partfun1('#skF_4',A_131)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_644])).

tff(c_649,plain,(
    ! [A_131,B_132] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_131)
      | ~ v1_partfun1('#skF_4',A_131)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_646])).

tff(c_758,plain,(
    ! [A_150,B_151] :
      ( ~ v1_partfun1('#skF_5',A_150)
      | ~ v1_partfun1('#skF_4',A_150)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_768,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_66,c_758])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_423,c_421,c_768])).

tff(c_785,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_800,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_60])).

tff(c_816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_800])).

tff(c_818,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_30,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_876,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | A_24 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_30])).

tff(c_817,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_824,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_817])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_819,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_2])).

tff(c_829,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_819])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_834,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_818,c_10])).

tff(c_878,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_824,c_72])).

tff(c_1516,plain,(
    ! [C_235,B_236,A_237] :
      ( ~ v1_xboole_0(C_235)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(C_235))
      | ~ r2_hidden(A_237,B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1520,plain,(
    ! [A_237] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_237,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_878,c_1516])).

tff(c_1553,plain,(
    ! [A_239] : ~ r2_hidden(A_239,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_1520])).

tff(c_1558,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_876,c_1553])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_867,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_14])).

tff(c_1573,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_867])).

tff(c_2007,plain,(
    ! [A_306,B_307,C_308,D_309] :
      ( r2_relset_1(A_306,B_307,C_308,C_308)
      | ~ m1_subset_1(D_309,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2023,plain,(
    ! [A_311,B_312,C_313] :
      ( r2_relset_1(A_311,B_312,C_313,C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312))) ) ),
    inference(resolution,[status(thm)],[c_1573,c_2007])).

tff(c_2034,plain,(
    ! [A_311,B_312] : r2_relset_1(A_311,B_312,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1573,c_2023])).

tff(c_879,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_824,c_66])).

tff(c_1518,plain,(
    ! [A_237] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_237,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_879,c_1516])).

tff(c_1530,plain,(
    ! [A_238] : ~ r2_hidden(A_238,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_1518])).

tff(c_1535,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_876,c_1530])).

tff(c_869,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_60])).

tff(c_1541,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_869])).

tff(c_1686,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1558,c_1558,c_1541])).

tff(c_2037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_1686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.66/1.63  
% 3.66/1.63  %Foreground sorts:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Background operators:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Foreground operators:
% 3.66/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.66/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.66/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.63  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.66/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.66/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.66/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.63  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.66/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.63  
% 3.66/1.64  tff(f_177, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.66/1.64  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.66/1.64  tff(f_109, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.66/1.64  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.66/1.64  tff(f_144, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.66/1.64  tff(f_95, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.66/1.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.66/1.64  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.66/1.64  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.66/1.64  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.66/1.64  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_534, plain, (![A_124, B_125, C_126, D_127]: (r2_relset_1(A_124, B_125, C_126, C_126) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.64  tff(c_632, plain, (![C_128]: (r2_relset_1('#skF_2', '#skF_3', C_128, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_66, c_534])).
% 3.66/1.64  tff(c_641, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_632])).
% 3.66/1.64  tff(c_62, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_62])).
% 3.66/1.64  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_381, plain, (![C_116, A_117, B_118]: (v1_partfun1(C_116, A_117) | ~v1_funct_2(C_116, A_117, B_118) | ~v1_funct_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | v1_xboole_0(B_118))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.64  tff(c_387, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_381])).
% 3.66/1.64  tff(c_404, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_387])).
% 3.66/1.64  tff(c_410, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_404])).
% 3.66/1.64  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.66/1.64  tff(c_415, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_410, c_4])).
% 3.66/1.64  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_415])).
% 3.66/1.64  tff(c_422, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_404])).
% 3.66/1.64  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_390, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_381])).
% 3.66/1.64  tff(c_407, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_390])).
% 3.66/1.64  tff(c_423, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_422, c_407])).
% 3.66/1.64  tff(c_421, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_404])).
% 3.66/1.64  tff(c_64, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_644, plain, (![D_129, C_130, A_131, B_132]: (D_129=C_130 | ~r1_partfun1(C_130, D_129) | ~v1_partfun1(D_129, A_131) | ~v1_partfun1(C_130, A_131) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(D_129) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.66/1.64  tff(c_646, plain, (![A_131, B_132]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_131) | ~v1_partfun1('#skF_4', A_131) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_644])).
% 3.66/1.64  tff(c_649, plain, (![A_131, B_132]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_131) | ~v1_partfun1('#skF_4', A_131) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_646])).
% 3.66/1.64  tff(c_758, plain, (![A_150, B_151]: (~v1_partfun1('#skF_5', A_150) | ~v1_partfun1('#skF_4', A_150) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(splitLeft, [status(thm)], [c_649])).
% 3.66/1.64  tff(c_768, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_66, c_758])).
% 3.66/1.64  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_423, c_421, c_768])).
% 3.66/1.64  tff(c_785, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_649])).
% 3.66/1.64  tff(c_60, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.66/1.64  tff(c_800, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_785, c_60])).
% 3.66/1.64  tff(c_816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_800])).
% 3.66/1.64  tff(c_818, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_62])).
% 3.66/1.64  tff(c_30, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.66/1.64  tff(c_876, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | A_24='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_30])).
% 3.66/1.64  tff(c_817, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 3.66/1.64  tff(c_824, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_818, c_817])).
% 3.66/1.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.66/1.64  tff(c_819, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_2])).
% 3.66/1.64  tff(c_829, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_819])).
% 3.66/1.64  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.64  tff(c_834, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_818, c_10])).
% 3.66/1.64  tff(c_878, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_824, c_72])).
% 3.66/1.64  tff(c_1516, plain, (![C_235, B_236, A_237]: (~v1_xboole_0(C_235) | ~m1_subset_1(B_236, k1_zfmisc_1(C_235)) | ~r2_hidden(A_237, B_236))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.64  tff(c_1520, plain, (![A_237]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_237, '#skF_4'))), inference(resolution, [status(thm)], [c_878, c_1516])).
% 3.66/1.64  tff(c_1553, plain, (![A_239]: (~r2_hidden(A_239, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_829, c_1520])).
% 3.66/1.64  tff(c_1558, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_876, c_1553])).
% 3.66/1.64  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.64  tff(c_867, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_14])).
% 3.66/1.64  tff(c_1573, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_867])).
% 3.66/1.64  tff(c_2007, plain, (![A_306, B_307, C_308, D_309]: (r2_relset_1(A_306, B_307, C_308, C_308) | ~m1_subset_1(D_309, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.64  tff(c_2023, plain, (![A_311, B_312, C_313]: (r2_relset_1(A_311, B_312, C_313, C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))))), inference(resolution, [status(thm)], [c_1573, c_2007])).
% 3.66/1.64  tff(c_2034, plain, (![A_311, B_312]: (r2_relset_1(A_311, B_312, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1573, c_2023])).
% 3.66/1.64  tff(c_879, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_824, c_66])).
% 3.66/1.64  tff(c_1518, plain, (![A_237]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_237, '#skF_5'))), inference(resolution, [status(thm)], [c_879, c_1516])).
% 3.66/1.64  tff(c_1530, plain, (![A_238]: (~r2_hidden(A_238, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_829, c_1518])).
% 3.66/1.64  tff(c_1535, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_876, c_1530])).
% 3.66/1.64  tff(c_869, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_60])).
% 3.66/1.64  tff(c_1541, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_869])).
% 3.66/1.64  tff(c_1686, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1558, c_1558, c_1541])).
% 3.66/1.64  tff(c_2037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2034, c_1686])).
% 3.66/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.64  
% 3.66/1.64  Inference rules
% 3.66/1.64  ----------------------
% 3.66/1.64  #Ref     : 0
% 3.66/1.64  #Sup     : 393
% 3.66/1.64  #Fact    : 0
% 3.66/1.64  #Define  : 0
% 3.66/1.64  #Split   : 20
% 3.66/1.64  #Chain   : 0
% 3.66/1.65  #Close   : 0
% 3.66/1.65  
% 3.66/1.65  Ordering : KBO
% 3.66/1.65  
% 3.66/1.65  Simplification rules
% 3.66/1.65  ----------------------
% 3.66/1.65  #Subsume      : 67
% 3.66/1.65  #Demod        : 545
% 3.66/1.65  #Tautology    : 246
% 3.66/1.65  #SimpNegUnit  : 25
% 3.66/1.65  #BackRed      : 129
% 3.66/1.65  
% 3.66/1.65  #Partial instantiations: 0
% 3.66/1.65  #Strategies tried      : 1
% 3.66/1.65  
% 3.66/1.65  Timing (in seconds)
% 3.66/1.65  ----------------------
% 3.66/1.65  Preprocessing        : 0.34
% 3.66/1.65  Parsing              : 0.18
% 3.66/1.65  CNF conversion       : 0.02
% 3.66/1.65  Main loop            : 0.54
% 3.66/1.65  Inferencing          : 0.18
% 3.66/1.65  Reduction            : 0.18
% 3.66/1.65  Demodulation         : 0.13
% 3.66/1.65  BG Simplification    : 0.03
% 3.66/1.65  Subsumption          : 0.09
% 3.66/1.65  Abstraction          : 0.02
% 3.66/1.65  MUC search           : 0.00
% 3.66/1.65  Cooper               : 0.00
% 3.66/1.65  Total                : 0.91
% 3.66/1.65  Index Insertion      : 0.00
% 4.00/1.65  Index Deletion       : 0.00
% 4.00/1.65  Index Matching       : 0.00
% 4.00/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
