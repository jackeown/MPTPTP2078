%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 430 expanded)
%              Number of leaves         :   32 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 (1346 expanded)
%              Number of equality atoms :   32 ( 384 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_114,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_91,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_193,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( r2_relset_1(A_58,B_59,C_60,C_60)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    ! [C_68] :
      ( r2_relset_1('#skF_4','#skF_5',C_68,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_193])).

tff(c_245,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_236])).

tff(c_74,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_74])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_82,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_51])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_265,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_partfun1(C_71,A_72)
      | ~ v1_funct_2(C_71,A_72,B_73)
      | ~ v1_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | v1_xboole_0(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_272,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_265])).

tff(c_285,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_272])).

tff(c_290,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,(
    ! [A_10] :
      ( A_10 = '#skF_3'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_293,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_290,c_79])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_293])).

tff(c_298,plain,(
    v1_partfun1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_299,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_275,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_265])).

tff(c_288,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_275])).

tff(c_300,plain,(
    v1_partfun1('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_288])).

tff(c_38,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_330,plain,(
    ! [D_79,C_80,A_81,B_82] :
      ( D_79 = C_80
      | ~ r1_partfun1(C_80,D_79)
      | ~ v1_partfun1(D_79,A_81)
      | ~ v1_partfun1(C_80,A_81)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1(D_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_332,plain,(
    ! [A_81,B_82] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_81)
      | ~ v1_partfun1('#skF_6',A_81)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_330])).

tff(c_335,plain,(
    ! [A_81,B_82] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_81)
      | ~ v1_partfun1('#skF_6',A_81)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_332])).

tff(c_601,plain,(
    ! [A_126,B_127] :
      ( ~ v1_partfun1('#skF_7',A_126)
      | ~ v1_partfun1('#skF_6',A_126)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_607,plain,
    ( ~ v1_partfun1('#skF_7','#skF_4')
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_40,c_601])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_298,c_300,c_607])).

tff(c_619,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_625,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_34])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_625])).

tff(c_636,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_674,plain,(
    ! [A_130] :
      ( A_130 = '#skF_4'
      | ~ v1_xboole_0(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_12])).

tff(c_678,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_674])).

tff(c_679,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_14])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_648,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_4',B_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_636,c_20])).

tff(c_637,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_642,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_637])).

tff(c_696,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_642,c_40])).

tff(c_698,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(A_134,B_135)
      | ~ m1_subset_1(A_134,k1_zfmisc_1(B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_706,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_696,c_698])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_737,plain,(
    ! [C_147,B_148,A_149] :
      ( r2_hidden(C_147,B_148)
      | ~ r2_hidden(C_147,A_149)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_744,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_1'(A_150),B_151)
      | ~ r1_tarski(A_150,B_151)
      | v1_xboole_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_4,c_737])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_752,plain,(
    ! [B_152,A_153] :
      ( ~ v1_xboole_0(B_152)
      | ~ r1_tarski(A_153,B_152)
      | v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_744,c_2])).

tff(c_761,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_706,c_752])).

tff(c_769,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_761])).

tff(c_673,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_12])).

tff(c_776,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_769,c_673])).

tff(c_796,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_696])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_657,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_636,c_18])).

tff(c_827,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( r2_relset_1(A_157,B_158,C_159,C_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_832,plain,(
    ! [A_11,C_159,D_160] :
      ( r2_relset_1(A_11,'#skF_4',C_159,C_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_11,'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_827])).

tff(c_836,plain,(
    ! [A_11,C_159,D_160] :
      ( r2_relset_1(A_11,'#skF_4',C_159,C_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_159,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_832])).

tff(c_873,plain,(
    ! [D_160] : ~ m1_subset_1(D_160,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_836])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_796])).

tff(c_877,plain,(
    ! [A_174,C_175] :
      ( r2_relset_1(A_174,'#skF_4',C_175,C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_836])).

tff(c_883,plain,(
    ! [A_174] : r2_relset_1(A_174,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_796,c_877])).

tff(c_697,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_642,c_46])).

tff(c_705,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_697,c_698])).

tff(c_764,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_705,c_752])).

tff(c_772,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_764])).

tff(c_780,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_772,c_673])).

tff(c_690,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_34])).

tff(c_797,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_690])).

tff(c_838,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_797])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:07:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.11/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.11/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.11/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.11/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.11/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.47  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.18/1.49  tff(f_44, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.18/1.49  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.18/1.49  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.18/1.49  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.18/1.49  tff(f_74, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.18/1.49  tff(f_91, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.18/1.49  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.18/1.49  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.18/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.18/1.49  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.18/1.49  tff(c_14, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.18/1.49  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_193, plain, (![A_58, B_59, C_60, D_61]: (r2_relset_1(A_58, B_59, C_60, C_60) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.49  tff(c_236, plain, (![C_68]: (r2_relset_1('#skF_4', '#skF_5', C_68, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_40, c_193])).
% 3.18/1.49  tff(c_245, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_236])).
% 3.18/1.49  tff(c_74, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.18/1.49  tff(c_78, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14, c_74])).
% 3.18/1.49  tff(c_36, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_51, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_36])).
% 3.18/1.49  tff(c_82, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_51])).
% 3.18/1.49  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_265, plain, (![C_71, A_72, B_73]: (v1_partfun1(C_71, A_72) | ~v1_funct_2(C_71, A_72, B_73) | ~v1_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | v1_xboole_0(B_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.18/1.49  tff(c_272, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_265])).
% 3.18/1.49  tff(c_285, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_272])).
% 3.18/1.49  tff(c_290, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_285])).
% 3.18/1.49  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.18/1.49  tff(c_79, plain, (![A_10]: (A_10='#skF_3' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_12])).
% 3.18/1.49  tff(c_293, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_290, c_79])).
% 3.18/1.49  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_293])).
% 3.18/1.49  tff(c_298, plain, (v1_partfun1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_285])).
% 3.18/1.49  tff(c_299, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_285])).
% 3.18/1.49  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_42, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_275, plain, (v1_partfun1('#skF_7', '#skF_4') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_265])).
% 3.18/1.49  tff(c_288, plain, (v1_partfun1('#skF_7', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_275])).
% 3.18/1.49  tff(c_300, plain, (v1_partfun1('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_299, c_288])).
% 3.18/1.49  tff(c_38, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_330, plain, (![D_79, C_80, A_81, B_82]: (D_79=C_80 | ~r1_partfun1(C_80, D_79) | ~v1_partfun1(D_79, A_81) | ~v1_partfun1(C_80, A_81) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1(D_79) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_332, plain, (![A_81, B_82]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_81) | ~v1_partfun1('#skF_6', A_81) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_330])).
% 3.18/1.49  tff(c_335, plain, (![A_81, B_82]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_81) | ~v1_partfun1('#skF_6', A_81) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_332])).
% 3.18/1.49  tff(c_601, plain, (![A_126, B_127]: (~v1_partfun1('#skF_7', A_126) | ~v1_partfun1('#skF_6', A_126) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(splitLeft, [status(thm)], [c_335])).
% 3.18/1.49  tff(c_607, plain, (~v1_partfun1('#skF_7', '#skF_4') | ~v1_partfun1('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_40, c_601])).
% 3.18/1.49  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_298, c_300, c_607])).
% 3.18/1.49  tff(c_619, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_335])).
% 3.18/1.49  tff(c_34, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.18/1.49  tff(c_625, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_34])).
% 3.18/1.49  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_625])).
% 3.18/1.49  tff(c_636, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 3.18/1.49  tff(c_674, plain, (![A_130]: (A_130='#skF_4' | ~v1_xboole_0(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_12])).
% 3.18/1.49  tff(c_678, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_14, c_674])).
% 3.18/1.49  tff(c_679, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_14])).
% 3.18/1.49  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.18/1.49  tff(c_648, plain, (![B_12]: (k2_zfmisc_1('#skF_4', B_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_636, c_20])).
% 3.18/1.49  tff(c_637, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 3.18/1.49  tff(c_642, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_636, c_637])).
% 3.18/1.49  tff(c_696, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_642, c_40])).
% 3.18/1.49  tff(c_698, plain, (![A_134, B_135]: (r1_tarski(A_134, B_135) | ~m1_subset_1(A_134, k1_zfmisc_1(B_135)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.18/1.49  tff(c_706, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_696, c_698])).
% 3.18/1.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.49  tff(c_737, plain, (![C_147, B_148, A_149]: (r2_hidden(C_147, B_148) | ~r2_hidden(C_147, A_149) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.49  tff(c_744, plain, (![A_150, B_151]: (r2_hidden('#skF_1'(A_150), B_151) | ~r1_tarski(A_150, B_151) | v1_xboole_0(A_150))), inference(resolution, [status(thm)], [c_4, c_737])).
% 3.18/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.49  tff(c_752, plain, (![B_152, A_153]: (~v1_xboole_0(B_152) | ~r1_tarski(A_153, B_152) | v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_744, c_2])).
% 3.18/1.49  tff(c_761, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_706, c_752])).
% 3.18/1.49  tff(c_769, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_761])).
% 3.18/1.49  tff(c_673, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_12])).
% 3.18/1.49  tff(c_776, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_769, c_673])).
% 3.18/1.49  tff(c_796, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_776, c_696])).
% 3.18/1.49  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.18/1.49  tff(c_657, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_636, c_18])).
% 3.18/1.49  tff(c_827, plain, (![A_157, B_158, C_159, D_160]: (r2_relset_1(A_157, B_158, C_159, C_159) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.49  tff(c_832, plain, (![A_11, C_159, D_160]: (r2_relset_1(A_11, '#skF_4', C_159, C_159) | ~m1_subset_1(D_160, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_11, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_657, c_827])).
% 3.18/1.49  tff(c_836, plain, (![A_11, C_159, D_160]: (r2_relset_1(A_11, '#skF_4', C_159, C_159) | ~m1_subset_1(D_160, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_159, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_832])).
% 3.18/1.49  tff(c_873, plain, (![D_160]: (~m1_subset_1(D_160, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_836])).
% 3.18/1.49  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_873, c_796])).
% 3.18/1.49  tff(c_877, plain, (![A_174, C_175]: (r2_relset_1(A_174, '#skF_4', C_175, C_175) | ~m1_subset_1(C_175, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_836])).
% 3.18/1.49  tff(c_883, plain, (![A_174]: (r2_relset_1(A_174, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_796, c_877])).
% 3.18/1.49  tff(c_697, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_642, c_46])).
% 3.18/1.49  tff(c_705, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_697, c_698])).
% 3.18/1.49  tff(c_764, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_705, c_752])).
% 3.18/1.49  tff(c_772, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_764])).
% 3.18/1.49  tff(c_780, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_772, c_673])).
% 3.18/1.49  tff(c_690, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_34])).
% 3.18/1.49  tff(c_797, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_690])).
% 3.18/1.49  tff(c_838, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_797])).
% 3.18/1.49  tff(c_887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_883, c_838])).
% 3.18/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  Inference rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Ref     : 0
% 3.18/1.49  #Sup     : 178
% 3.18/1.49  #Fact    : 0
% 3.18/1.49  #Define  : 0
% 3.18/1.49  #Split   : 8
% 3.18/1.49  #Chain   : 0
% 3.18/1.49  #Close   : 0
% 3.18/1.49  
% 3.18/1.49  Ordering : KBO
% 3.18/1.49  
% 3.18/1.49  Simplification rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Subsume      : 32
% 3.18/1.49  #Demod        : 109
% 3.18/1.49  #Tautology    : 75
% 3.18/1.49  #SimpNegUnit  : 9
% 3.18/1.49  #BackRed      : 28
% 3.18/1.49  
% 3.18/1.49  #Partial instantiations: 0
% 3.18/1.49  #Strategies tried      : 1
% 3.18/1.49  
% 3.18/1.49  Timing (in seconds)
% 3.18/1.49  ----------------------
% 3.18/1.50  Preprocessing        : 0.32
% 3.18/1.50  Parsing              : 0.17
% 3.18/1.50  CNF conversion       : 0.02
% 3.18/1.50  Main loop            : 0.40
% 3.18/1.50  Inferencing          : 0.14
% 3.18/1.50  Reduction            : 0.12
% 3.18/1.50  Demodulation         : 0.08
% 3.18/1.50  BG Simplification    : 0.02
% 3.18/1.50  Subsumption          : 0.08
% 3.18/1.50  Abstraction          : 0.01
% 3.18/1.50  MUC search           : 0.00
% 3.18/1.50  Cooper               : 0.00
% 3.18/1.50  Total                : 0.76
% 3.18/1.50  Index Insertion      : 0.00
% 3.18/1.50  Index Deletion       : 0.00
% 3.18/1.50  Index Matching       : 0.00
% 3.18/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
