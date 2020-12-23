%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   99 (1390 expanded)
%              Number of leaves         :   30 ( 458 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 (3210 expanded)
%              Number of equality atoms :   48 ( 615 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_93,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44])).

tff(c_46,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( v1_xboole_0(k2_zfmisc_1(A_13,B_14))
      | ~ v1_xboole_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_72,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_530,plain,(
    ! [B_121,C_122,A_123] :
      ( k1_xboole_0 = B_121
      | v1_funct_2(C_122,A_123,B_121)
      | k1_relset_1(A_123,B_121,C_122) != A_123
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_545,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_530])).

tff(c_549,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_545])).

tff(c_550,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_549])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_568,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_12])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_568])).

tff(c_571,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_573,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_2'(A_124,B_125),A_124)
      | r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_577,plain,(
    ! [A_124,B_125] :
      ( ~ v1_xboole_0(A_124)
      | r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_573,c_2])).

tff(c_20,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_579,plain,(
    ! [B_128,A_129] :
      ( B_128 = A_129
      | ~ r1_tarski(B_128,A_129)
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_592,plain,(
    ! [A_130] :
      ( k1_xboole_0 = A_130
      | ~ r1_tarski(A_130,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_579])).

tff(c_610,plain,(
    ! [A_131] :
      ( k1_xboole_0 = A_131
      | ~ v1_xboole_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_577,c_592])).

tff(c_624,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_571,c_610])).

tff(c_572,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_623,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_572,c_610])).

tff(c_637,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_623])).

tff(c_639,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_48])).

tff(c_42,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1794,plain,(
    ! [B_271,A_272,C_273] :
      ( B_271 = '#skF_5'
      | k1_relset_1(A_272,B_271,C_273) = A_272
      | ~ v1_funct_2(C_273,A_272,B_271)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_272,B_271))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_42])).

tff(c_1812,plain,(
    ! [C_273] :
      ( '#skF_5' = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_273) = '#skF_3'
      | ~ v1_funct_2(C_273,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_273,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_1794])).

tff(c_1827,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1812])).

tff(c_625,plain,(
    ! [A_13,B_14] :
      ( k2_zfmisc_1(A_13,B_14) = k1_xboole_0
      | ~ v1_xboole_0(B_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_610])).

tff(c_695,plain,(
    ! [A_137,B_138] :
      ( k2_zfmisc_1(A_137,B_138) = '#skF_5'
      | ~ v1_xboole_0(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_625])).

tff(c_700,plain,(
    ! [A_137] : k2_zfmisc_1(A_137,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_571,c_695])).

tff(c_787,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_partfun1(C_155,A_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_812,plain,(
    ! [C_160,A_161] :
      ( v1_partfun1(C_160,A_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1('#skF_5'))
      | ~ v1_xboole_0(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_787])).

tff(c_815,plain,(
    ! [A_161] :
      ( v1_partfun1('#skF_5',A_161)
      | ~ v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_639,c_812])).

tff(c_1328,plain,(
    ! [C_229,A_230,B_231] :
      ( v1_funct_2(C_229,A_230,B_231)
      | ~ v1_partfun1(C_229,A_230)
      | ~ v1_funct_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1380,plain,(
    ! [C_236,A_237] :
      ( v1_funct_2(C_236,A_237,'#skF_5')
      | ~ v1_partfun1(C_236,A_237)
      | ~ v1_funct_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_1328])).

tff(c_1382,plain,(
    ! [A_237] :
      ( v1_funct_2('#skF_5',A_237,'#skF_5')
      | ~ v1_partfun1('#skF_5',A_237)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_639,c_1380])).

tff(c_1386,plain,(
    ! [A_238] :
      ( v1_funct_2('#skF_5',A_238,'#skF_5')
      | ~ v1_partfun1('#skF_5',A_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1382])).

tff(c_40,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_934,plain,(
    ! [B_193,C_194] :
      ( k1_relset_1('#skF_5',B_193,C_194) = '#skF_5'
      | ~ v1_funct_2(C_194,'#skF_5',B_193)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_193))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_624,c_624,c_624,c_40])).

tff(c_971,plain,(
    ! [C_200] :
      ( k1_relset_1('#skF_5','#skF_5',C_200) = '#skF_5'
      | ~ v1_funct_2(C_200,'#skF_5','#skF_5')
      | ~ m1_subset_1(C_200,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_934])).

tff(c_975,plain,
    ( k1_relset_1('#skF_5','#skF_5','#skF_5') = '#skF_5'
    | ~ v1_funct_2('#skF_5','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_639,c_971])).

tff(c_976,plain,(
    ~ v1_funct_2('#skF_5','#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_975])).

tff(c_1392,plain,(
    ~ v1_partfun1('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_1386,c_976])).

tff(c_1399,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_815,c_1392])).

tff(c_1403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_1399])).

tff(c_1405,plain,(
    v1_funct_2('#skF_5','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_975])).

tff(c_1837,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_1827,c_1827,c_1405])).

tff(c_32,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_25,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_850,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_5',A_25,'#skF_5')
      | A_25 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_700,c_624,c_624,c_624,c_624,c_624,c_32])).

tff(c_2058,plain,(
    ! [A_286] :
      ( v1_funct_2('#skF_4',A_286,'#skF_4')
      | A_286 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_1827,c_1827,c_850])).

tff(c_1857,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_52])).

tff(c_2062,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2058,c_1857])).

tff(c_2064,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_1857])).

tff(c_2070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_2064])).

tff(c_2072,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1812])).

tff(c_38,plain,(
    ! [B_26,C_27,A_25] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_25,B_26)
      | k1_relset_1(A_25,B_26,C_27) != A_25
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2080,plain,(
    ! [B_288,C_289,A_290] :
      ( B_288 = '#skF_5'
      | v1_funct_2(C_289,A_290,B_288)
      | k1_relset_1(A_290,B_288,C_289) != A_290
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_288))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_38])).

tff(c_2098,plain,(
    ! [C_289] :
      ( '#skF_5' = '#skF_4'
      | v1_funct_2(C_289,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_289) != '#skF_3'
      | ~ m1_subset_1(C_289,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_2080])).

tff(c_2101,plain,(
    ! [C_291] :
      ( v1_funct_2(C_291,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_291) != '#skF_3'
      | ~ m1_subset_1(C_291,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2072,c_2098])).

tff(c_2104,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_639,c_2101])).

tff(c_2107,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2104])).

tff(c_2109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.69  
% 3.93/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.70  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.93/1.70  
% 3.93/1.70  %Foreground sorts:
% 3.93/1.70  
% 3.93/1.70  
% 3.93/1.70  %Background operators:
% 3.93/1.70  
% 3.93/1.70  
% 3.93/1.70  %Foreground operators:
% 3.93/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.93/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.93/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.93/1.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.93/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.93/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.93/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.93/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.93/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.93/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.70  
% 3.93/1.71  tff(f_106, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.93/1.71  tff(f_51, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.93/1.71  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.93/1.71  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.93/1.71  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.93/1.71  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.93/1.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.93/1.71  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.93/1.71  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.93/1.71  tff(f_75, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.93/1.71  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.93/1.71  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.93/1.71  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.93/1.71  tff(c_44, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.93/1.71  tff(c_52, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44])).
% 3.93/1.71  tff(c_46, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.93/1.71  tff(c_22, plain, (![A_13, B_14]: (v1_xboole_0(k2_zfmisc_1(A_13, B_14)) | ~v1_xboole_0(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.93/1.71  tff(c_67, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.93/1.71  tff(c_71, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_67])).
% 3.93/1.71  tff(c_72, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_71])).
% 3.93/1.71  tff(c_76, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_22, c_72])).
% 3.93/1.71  tff(c_530, plain, (![B_121, C_122, A_123]: (k1_xboole_0=B_121 | v1_funct_2(C_122, A_123, B_121) | k1_relset_1(A_123, B_121, C_122)!=A_123 | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_121))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.93/1.71  tff(c_545, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_530])).
% 3.93/1.71  tff(c_549, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_545])).
% 3.93/1.71  tff(c_550, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_549])).
% 3.93/1.71  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.93/1.71  tff(c_568, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_12])).
% 3.93/1.71  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_568])).
% 3.93/1.71  tff(c_571, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_71])).
% 3.93/1.71  tff(c_573, plain, (![A_124, B_125]: (r2_hidden('#skF_2'(A_124, B_125), A_124) | r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.93/1.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.71  tff(c_577, plain, (![A_124, B_125]: (~v1_xboole_0(A_124) | r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_573, c_2])).
% 3.93/1.71  tff(c_20, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.93/1.71  tff(c_579, plain, (![B_128, A_129]: (B_128=A_129 | ~r1_tarski(B_128, A_129) | ~r1_tarski(A_129, B_128))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.93/1.71  tff(c_592, plain, (![A_130]: (k1_xboole_0=A_130 | ~r1_tarski(A_130, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_579])).
% 3.93/1.71  tff(c_610, plain, (![A_131]: (k1_xboole_0=A_131 | ~v1_xboole_0(A_131))), inference(resolution, [status(thm)], [c_577, c_592])).
% 3.93/1.71  tff(c_624, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_571, c_610])).
% 3.93/1.71  tff(c_572, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_71])).
% 3.93/1.71  tff(c_623, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_572, c_610])).
% 3.93/1.71  tff(c_637, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_624, c_623])).
% 3.93/1.71  tff(c_639, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_48])).
% 3.93/1.71  tff(c_42, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.93/1.71  tff(c_1794, plain, (![B_271, A_272, C_273]: (B_271='#skF_5' | k1_relset_1(A_272, B_271, C_273)=A_272 | ~v1_funct_2(C_273, A_272, B_271) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_42])).
% 3.93/1.71  tff(c_1812, plain, (![C_273]: ('#skF_5'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_273)='#skF_3' | ~v1_funct_2(C_273, '#skF_3', '#skF_4') | ~m1_subset_1(C_273, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_637, c_1794])).
% 3.93/1.71  tff(c_1827, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1812])).
% 3.93/1.71  tff(c_625, plain, (![A_13, B_14]: (k2_zfmisc_1(A_13, B_14)=k1_xboole_0 | ~v1_xboole_0(B_14))), inference(resolution, [status(thm)], [c_22, c_610])).
% 3.93/1.71  tff(c_695, plain, (![A_137, B_138]: (k2_zfmisc_1(A_137, B_138)='#skF_5' | ~v1_xboole_0(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_625])).
% 3.93/1.71  tff(c_700, plain, (![A_137]: (k2_zfmisc_1(A_137, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_571, c_695])).
% 3.93/1.71  tff(c_787, plain, (![C_155, A_156, B_157]: (v1_partfun1(C_155, A_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.93/1.71  tff(c_812, plain, (![C_160, A_161]: (v1_partfun1(C_160, A_161) | ~m1_subset_1(C_160, k1_zfmisc_1('#skF_5')) | ~v1_xboole_0(A_161))), inference(superposition, [status(thm), theory('equality')], [c_700, c_787])).
% 3.93/1.71  tff(c_815, plain, (![A_161]: (v1_partfun1('#skF_5', A_161) | ~v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_639, c_812])).
% 3.93/1.71  tff(c_1328, plain, (![C_229, A_230, B_231]: (v1_funct_2(C_229, A_230, B_231) | ~v1_partfun1(C_229, A_230) | ~v1_funct_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.93/1.71  tff(c_1380, plain, (![C_236, A_237]: (v1_funct_2(C_236, A_237, '#skF_5') | ~v1_partfun1(C_236, A_237) | ~v1_funct_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_700, c_1328])).
% 3.93/1.71  tff(c_1382, plain, (![A_237]: (v1_funct_2('#skF_5', A_237, '#skF_5') | ~v1_partfun1('#skF_5', A_237) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_639, c_1380])).
% 3.93/1.71  tff(c_1386, plain, (![A_238]: (v1_funct_2('#skF_5', A_238, '#skF_5') | ~v1_partfun1('#skF_5', A_238))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1382])).
% 3.93/1.71  tff(c_40, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.93/1.71  tff(c_934, plain, (![B_193, C_194]: (k1_relset_1('#skF_5', B_193, C_194)='#skF_5' | ~v1_funct_2(C_194, '#skF_5', B_193) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_193))))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_624, c_624, c_624, c_40])).
% 3.93/1.71  tff(c_971, plain, (![C_200]: (k1_relset_1('#skF_5', '#skF_5', C_200)='#skF_5' | ~v1_funct_2(C_200, '#skF_5', '#skF_5') | ~m1_subset_1(C_200, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_700, c_934])).
% 3.93/1.71  tff(c_975, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_5')='#skF_5' | ~v1_funct_2('#skF_5', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_639, c_971])).
% 3.93/1.71  tff(c_976, plain, (~v1_funct_2('#skF_5', '#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_975])).
% 3.93/1.71  tff(c_1392, plain, (~v1_partfun1('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_1386, c_976])).
% 3.93/1.71  tff(c_1399, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_815, c_1392])).
% 3.93/1.71  tff(c_1403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_571, c_1399])).
% 3.93/1.71  tff(c_1405, plain, (v1_funct_2('#skF_5', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_975])).
% 3.93/1.71  tff(c_1837, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1827, c_1827, c_1827, c_1405])).
% 3.93/1.71  tff(c_32, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_25, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.93/1.71  tff(c_850, plain, (![A_25]: (v1_funct_2('#skF_5', A_25, '#skF_5') | A_25='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_700, c_624, c_624, c_624, c_624, c_624, c_32])).
% 3.93/1.71  tff(c_2058, plain, (![A_286]: (v1_funct_2('#skF_4', A_286, '#skF_4') | A_286='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1827, c_1827, c_1827, c_850])).
% 3.93/1.71  tff(c_1857, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1827, c_52])).
% 3.93/1.71  tff(c_2062, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2058, c_1857])).
% 3.93/1.71  tff(c_2064, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_1857])).
% 3.93/1.71  tff(c_2070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1837, c_2064])).
% 3.93/1.71  tff(c_2072, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_1812])).
% 3.93/1.71  tff(c_38, plain, (![B_26, C_27, A_25]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_25, B_26) | k1_relset_1(A_25, B_26, C_27)!=A_25 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.93/1.71  tff(c_2080, plain, (![B_288, C_289, A_290]: (B_288='#skF_5' | v1_funct_2(C_289, A_290, B_288) | k1_relset_1(A_290, B_288, C_289)!=A_290 | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_288))))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_38])).
% 3.93/1.71  tff(c_2098, plain, (![C_289]: ('#skF_5'='#skF_4' | v1_funct_2(C_289, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_289)!='#skF_3' | ~m1_subset_1(C_289, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_637, c_2080])).
% 3.93/1.71  tff(c_2101, plain, (![C_291]: (v1_funct_2(C_291, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_291)!='#skF_3' | ~m1_subset_1(C_291, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2072, c_2098])).
% 3.93/1.71  tff(c_2104, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_639, c_2101])).
% 3.93/1.71  tff(c_2107, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2104])).
% 3.93/1.71  tff(c_2109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2107])).
% 3.93/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.71  
% 3.93/1.71  Inference rules
% 3.93/1.71  ----------------------
% 3.93/1.71  #Ref     : 0
% 3.93/1.71  #Sup     : 490
% 3.93/1.71  #Fact    : 0
% 3.93/1.71  #Define  : 0
% 3.93/1.71  #Split   : 11
% 3.93/1.71  #Chain   : 0
% 3.93/1.71  #Close   : 0
% 3.93/1.71  
% 3.93/1.71  Ordering : KBO
% 3.93/1.71  
% 3.93/1.71  Simplification rules
% 3.93/1.71  ----------------------
% 3.93/1.71  #Subsume      : 192
% 3.93/1.71  #Demod        : 325
% 3.93/1.71  #Tautology    : 149
% 3.93/1.71  #SimpNegUnit  : 24
% 3.93/1.71  #BackRed      : 69
% 3.93/1.71  
% 3.93/1.71  #Partial instantiations: 0
% 3.93/1.71  #Strategies tried      : 1
% 3.93/1.71  
% 3.93/1.71  Timing (in seconds)
% 3.93/1.71  ----------------------
% 3.93/1.72  Preprocessing        : 0.34
% 3.93/1.72  Parsing              : 0.19
% 3.93/1.72  CNF conversion       : 0.02
% 3.93/1.72  Main loop            : 0.59
% 3.93/1.72  Inferencing          : 0.21
% 3.93/1.72  Reduction            : 0.16
% 3.93/1.72  Demodulation         : 0.11
% 3.93/1.72  BG Simplification    : 0.03
% 3.93/1.72  Subsumption          : 0.15
% 3.93/1.72  Abstraction          : 0.03
% 3.93/1.72  MUC search           : 0.00
% 3.93/1.72  Cooper               : 0.00
% 3.93/1.72  Total                : 0.97
% 3.93/1.72  Index Insertion      : 0.00
% 3.93/1.72  Index Deletion       : 0.00
% 3.93/1.72  Index Matching       : 0.00
% 3.93/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
