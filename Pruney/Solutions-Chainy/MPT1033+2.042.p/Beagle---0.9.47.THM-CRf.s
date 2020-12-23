%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 256 expanded)
%              Number of leaves         :   33 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 892 expanded)
%              Number of equality atoms :   28 ( 235 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_249,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_relset_1(A_76,B_77,C_78,C_78)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_273,plain,(
    ! [C_80] :
      ( r2_relset_1('#skF_3','#skF_4',C_80,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_249])).

tff(c_289,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_273])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_199,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_206,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_199])).

tff(c_227,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_206])).

tff(c_234,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_234,c_4])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_240])).

tff(c_246,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_247,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_209,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_199])).

tff(c_230,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_209])).

tff(c_248,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_230])).

tff(c_40,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_319,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r1_partfun1(C_87,D_86)
      | ~ v1_partfun1(D_86,A_88)
      | ~ v1_partfun1(C_87,A_88)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1(D_86)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_321,plain,(
    ! [A_88,B_89] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_88)
      | ~ v1_partfun1('#skF_5',A_88)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_319])).

tff(c_324,plain,(
    ! [A_88,B_89] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_88)
      | ~ v1_partfun1('#skF_5',A_88)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_321])).

tff(c_519,plain,(
    ! [A_107,B_108] :
      ( ~ v1_partfun1('#skF_6',A_107)
      | ~ v1_partfun1('#skF_5',A_107)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_522,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_48,c_519])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_246,c_248,c_522])).

tff(c_533,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_538,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_36])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_538])).

tff(c_549,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_569,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_12])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_820,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( r2_relset_1(A_153,B_154,C_155,C_155)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_837,plain,(
    ! [A_157,B_158,C_159] :
      ( r2_relset_1(A_157,B_158,C_159,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(resolution,[status(thm)],[c_16,c_820])).

tff(c_853,plain,(
    ! [A_157,B_158] : r2_relset_1(A_157,B_158,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_569,c_837])).

tff(c_24,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_607,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | A_17 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_24])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_557,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_548])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_552,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_2])).

tff(c_568,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_552])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_551,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_548,c_10])).

tff(c_578,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_557,c_551])).

tff(c_605,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_557,c_42])).

tff(c_621,plain,(
    ! [C_118,B_119,A_120] :
      ( ~ v1_xboole_0(C_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(C_118))
      | ~ r2_hidden(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_625,plain,(
    ! [A_120] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_120,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_605,c_621])).

tff(c_655,plain,(
    ! [A_122] : ~ r2_hidden(A_122,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_625])).

tff(c_660,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_607,c_655])).

tff(c_606,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_557,c_48])).

tff(c_623,plain,(
    ! [A_120] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_120,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_606,c_621])).

tff(c_638,plain,(
    ! [A_121] : ~ r2_hidden(A_121,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_623])).

tff(c_643,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_607,c_638])).

tff(c_603,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_36])).

tff(c_646,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_603])).

tff(c_685,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_646])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.49  %$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.18/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.49  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.18/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.18/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.18/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.18/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.18/1.49  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.18/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.49  
% 3.18/1.51  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 3.18/1.51  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.18/1.51  tff(f_93, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.18/1.51  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.18/1.51  tff(f_110, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 3.18/1.51  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.18/1.51  tff(f_44, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.18/1.51  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.18/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.18/1.51  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.18/1.51  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.18/1.51  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_249, plain, (![A_76, B_77, C_78, D_79]: (r2_relset_1(A_76, B_77, C_78, C_78) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.18/1.51  tff(c_273, plain, (![C_80]: (r2_relset_1('#skF_3', '#skF_4', C_80, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_42, c_249])).
% 3.18/1.51  tff(c_289, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_273])).
% 3.18/1.51  tff(c_38, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_66, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 3.18/1.51  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_199, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.18/1.51  tff(c_206, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_199])).
% 3.18/1.51  tff(c_227, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_206])).
% 3.18/1.51  tff(c_234, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_227])).
% 3.18/1.51  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.18/1.51  tff(c_240, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_234, c_4])).
% 3.18/1.51  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_240])).
% 3.18/1.51  tff(c_246, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_227])).
% 3.18/1.51  tff(c_247, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_227])).
% 3.18/1.51  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_209, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_199])).
% 3.18/1.51  tff(c_230, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_209])).
% 3.18/1.51  tff(c_248, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_247, c_230])).
% 3.18/1.51  tff(c_40, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_319, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r1_partfun1(C_87, D_86) | ~v1_partfun1(D_86, A_88) | ~v1_partfun1(C_87, A_88) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1(D_86) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.51  tff(c_321, plain, (![A_88, B_89]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_88) | ~v1_partfun1('#skF_5', A_88) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_319])).
% 3.18/1.51  tff(c_324, plain, (![A_88, B_89]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_88) | ~v1_partfun1('#skF_5', A_88) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_321])).
% 3.18/1.51  tff(c_519, plain, (![A_107, B_108]: (~v1_partfun1('#skF_6', A_107) | ~v1_partfun1('#skF_5', A_107) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(splitLeft, [status(thm)], [c_324])).
% 3.18/1.51  tff(c_522, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_48, c_519])).
% 3.18/1.51  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_246, c_248, c_522])).
% 3.18/1.51  tff(c_533, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_324])).
% 3.18/1.51  tff(c_36, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.18/1.51  tff(c_538, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_36])).
% 3.18/1.51  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_538])).
% 3.18/1.51  tff(c_549, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 3.18/1.51  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.51  tff(c_569, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_12])).
% 3.18/1.51  tff(c_16, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.18/1.51  tff(c_820, plain, (![A_153, B_154, C_155, D_156]: (r2_relset_1(A_153, B_154, C_155, C_155) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.18/1.51  tff(c_837, plain, (![A_157, B_158, C_159]: (r2_relset_1(A_157, B_158, C_159, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(resolution, [status(thm)], [c_16, c_820])).
% 3.18/1.51  tff(c_853, plain, (![A_157, B_158]: (r2_relset_1(A_157, B_158, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_569, c_837])).
% 3.18/1.51  tff(c_24, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.18/1.51  tff(c_607, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | A_17='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_549, c_24])).
% 3.18/1.51  tff(c_548, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.18/1.51  tff(c_557, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_549, c_548])).
% 3.18/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.18/1.51  tff(c_552, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_2])).
% 3.18/1.51  tff(c_568, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_552])).
% 3.18/1.51  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.18/1.51  tff(c_551, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_548, c_10])).
% 3.18/1.51  tff(c_578, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_557, c_551])).
% 3.18/1.51  tff(c_605, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_557, c_42])).
% 3.18/1.51  tff(c_621, plain, (![C_118, B_119, A_120]: (~v1_xboole_0(C_118) | ~m1_subset_1(B_119, k1_zfmisc_1(C_118)) | ~r2_hidden(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.51  tff(c_625, plain, (![A_120]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_120, '#skF_6'))), inference(resolution, [status(thm)], [c_605, c_621])).
% 3.18/1.51  tff(c_655, plain, (![A_122]: (~r2_hidden(A_122, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_568, c_625])).
% 3.18/1.51  tff(c_660, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_607, c_655])).
% 3.18/1.51  tff(c_606, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_557, c_48])).
% 3.18/1.51  tff(c_623, plain, (![A_120]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_120, '#skF_5'))), inference(resolution, [status(thm)], [c_606, c_621])).
% 3.18/1.51  tff(c_638, plain, (![A_121]: (~r2_hidden(A_121, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_568, c_623])).
% 3.18/1.51  tff(c_643, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_607, c_638])).
% 3.18/1.51  tff(c_603, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_36])).
% 3.18/1.51  tff(c_646, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_603])).
% 3.18/1.51  tff(c_685, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_660, c_646])).
% 3.18/1.51  tff(c_856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_853, c_685])).
% 3.18/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  Inference rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Ref     : 0
% 3.18/1.51  #Sup     : 179
% 3.18/1.51  #Fact    : 0
% 3.18/1.51  #Define  : 0
% 3.18/1.51  #Split   : 7
% 3.18/1.51  #Chain   : 0
% 3.18/1.51  #Close   : 0
% 3.18/1.51  
% 3.18/1.51  Ordering : KBO
% 3.18/1.51  
% 3.18/1.51  Simplification rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Subsume      : 25
% 3.18/1.51  #Demod        : 130
% 3.18/1.51  #Tautology    : 80
% 3.18/1.51  #SimpNegUnit  : 3
% 3.18/1.51  #BackRed      : 26
% 3.18/1.51  
% 3.18/1.51  #Partial instantiations: 0
% 3.18/1.51  #Strategies tried      : 1
% 3.18/1.51  
% 3.18/1.51  Timing (in seconds)
% 3.18/1.51  ----------------------
% 3.18/1.51  Preprocessing        : 0.31
% 3.18/1.51  Parsing              : 0.17
% 3.18/1.51  CNF conversion       : 0.02
% 3.18/1.52  Main loop            : 0.37
% 3.18/1.52  Inferencing          : 0.12
% 3.18/1.52  Reduction            : 0.12
% 3.18/1.52  Demodulation         : 0.08
% 3.18/1.52  BG Simplification    : 0.02
% 3.18/1.52  Subsumption          : 0.07
% 3.18/1.52  Abstraction          : 0.02
% 3.18/1.52  MUC search           : 0.00
% 3.18/1.52  Cooper               : 0.00
% 3.18/1.52  Total                : 0.72
% 3.18/1.52  Index Insertion      : 0.00
% 3.18/1.52  Index Deletion       : 0.00
% 3.18/1.52  Index Matching       : 0.00
% 3.18/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
