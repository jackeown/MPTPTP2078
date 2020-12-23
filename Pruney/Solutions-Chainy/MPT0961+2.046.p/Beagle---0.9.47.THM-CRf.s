%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 241 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 570 expanded)
%              Number of equality atoms :   62 ( 234 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_88,axiom,(
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

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_825,plain,(
    ! [C_161,A_162,B_163] :
      ( m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ r1_tarski(k2_relat_1(C_161),B_163)
      | ~ r1_tarski(k1_relat_1(C_161),A_162)
      | ~ v1_relat_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,(
    ! [C_61,A_62,B_63] :
      ( m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ r1_tarski(k2_relat_1(C_61),B_63)
      | ~ r1_tarski(k1_relat_1(C_61),A_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_323,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ r1_tarski(k2_relat_1(C_79),B_78)
      | ~ r1_tarski(k1_relat_1(C_79),A_77)
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_233,c_26])).

tff(c_332,plain,(
    ! [A_80,C_81] :
      ( k1_relset_1(A_80,k2_relat_1(C_81),C_81) = k1_relat_1(C_81)
      | ~ r1_tarski(k1_relat_1(C_81),A_80)
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_345,plain,(
    ! [C_81] :
      ( k1_relset_1(k1_relat_1(C_81),k2_relat_1(C_81),C_81) = k1_relat_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_332])).

tff(c_99,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_108,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_28,plain,(
    ! [C_18,A_16,B_17] :
      ( m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ r1_tarski(k2_relat_1(C_18),B_17)
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_297,plain,(
    ! [B_72,C_73,A_74] :
      ( k1_xboole_0 = B_72
      | v1_funct_2(C_73,A_74,B_72)
      | k1_relset_1(A_74,B_72,C_73) != A_74
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_400,plain,(
    ! [B_91,C_92,A_93] :
      ( k1_xboole_0 = B_91
      | v1_funct_2(C_92,A_93,B_91)
      | k1_relset_1(A_93,B_91,C_92) != A_93
      | ~ r1_tarski(k2_relat_1(C_92),B_91)
      | ~ r1_tarski(k1_relat_1(C_92),A_93)
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_28,c_297])).

tff(c_409,plain,(
    ! [C_94,A_95] :
      ( k2_relat_1(C_94) = k1_xboole_0
      | v1_funct_2(C_94,A_95,k2_relat_1(C_94))
      | k1_relset_1(A_95,k2_relat_1(C_94),C_94) != A_95
      | ~ r1_tarski(k1_relat_1(C_94),A_95)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_400])).

tff(c_44,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_71,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_419,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_409,c_71])).

tff(c_429,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_419])).

tff(c_430,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_429])).

tff(c_435,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_430])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_435])).

tff(c_440,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_450,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_440,c_20])).

tff(c_89,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_98,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_442,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_98])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_442])).

tff(c_468,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_469,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_491,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_469])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_484,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_10])).

tff(c_609,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_616,plain,(
    ! [A_115,B_116] : k1_relset_1(A_115,B_116,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_484,c_609])).

tff(c_618,plain,(
    ! [A_115,B_116] : k1_relset_1(A_115,B_116,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_616])).

tff(c_72,plain,(
    ! [A_28,B_29] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_28,B_29)),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [B_29] : k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_29)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_481,plain,(
    ! [B_29] : k1_relat_1(k2_zfmisc_1('#skF_1',B_29)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_468,c_77])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_8,B_9] :
      ( k1_relat_1(k2_zfmisc_1(A_8,B_9)) != k1_xboole_0
      | k2_zfmisc_1(A_8,B_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_576,plain,(
    ! [A_110,B_111] :
      ( k1_relat_1(k2_zfmisc_1(A_110,B_111)) != '#skF_1'
      | k2_zfmisc_1(A_110,B_111) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_468,c_96])).

tff(c_580,plain,(
    ! [B_29] : k2_zfmisc_1('#skF_1',B_29) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_576])).

tff(c_34,plain,(
    ! [C_21,B_20] :
      ( v1_funct_2(C_21,k1_xboole_0,B_20)
      | k1_relset_1(k1_xboole_0,B_20,C_21) != k1_xboole_0
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_652,plain,(
    ! [C_126,B_127] :
      ( v1_funct_2(C_126,'#skF_1',B_127)
      | k1_relset_1('#skF_1',B_127,C_126) != '#skF_1'
      | ~ m1_subset_1(C_126,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_468,c_468,c_468,c_468,c_34])).

tff(c_655,plain,(
    ! [B_127] :
      ( v1_funct_2('#skF_1','#skF_1',B_127)
      | k1_relset_1('#skF_1',B_127,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_484,c_652])).

tff(c_658,plain,(
    ! [B_127] : v1_funct_2('#skF_1','#skF_1',B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_655])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_485,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_468,c_18])).

tff(c_492,plain,(
    ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_71])).

tff(c_516,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_492])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_516])).

tff(c_662,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_837,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_825,c_662])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_6,c_837])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.97  
% 3.53/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.98  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.53/1.98  
% 3.53/1.98  %Foreground sorts:
% 3.53/1.98  
% 3.53/1.98  
% 3.53/1.98  %Background operators:
% 3.53/1.98  
% 3.53/1.98  
% 3.53/1.98  %Foreground operators:
% 3.53/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.98  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.98  
% 3.80/2.00  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.80/2.00  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.80/2.00  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.80/2.00  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.80/2.00  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.80/2.00  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.80/2.00  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.80/2.00  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.80/2.00  tff(f_47, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 3.80/2.00  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.80/2.00  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.80/2.00  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.80/2.00  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.80/2.00  tff(c_825, plain, (![C_161, A_162, B_163]: (m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~r1_tarski(k2_relat_1(C_161), B_163) | ~r1_tarski(k1_relat_1(C_161), A_162) | ~v1_relat_1(C_161))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.80/2.00  tff(c_233, plain, (![C_61, A_62, B_63]: (m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~r1_tarski(k2_relat_1(C_61), B_63) | ~r1_tarski(k1_relat_1(C_61), A_62) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.80/2.00  tff(c_26, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/2.00  tff(c_323, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~r1_tarski(k2_relat_1(C_79), B_78) | ~r1_tarski(k1_relat_1(C_79), A_77) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_233, c_26])).
% 3.80/2.00  tff(c_332, plain, (![A_80, C_81]: (k1_relset_1(A_80, k2_relat_1(C_81), C_81)=k1_relat_1(C_81) | ~r1_tarski(k1_relat_1(C_81), A_80) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_6, c_323])).
% 3.80/2.00  tff(c_345, plain, (![C_81]: (k1_relset_1(k1_relat_1(C_81), k2_relat_1(C_81), C_81)=k1_relat_1(C_81) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_6, c_332])).
% 3.80/2.00  tff(c_99, plain, (![A_32]: (k2_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/2.00  tff(c_107, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_99])).
% 3.80/2.00  tff(c_108, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_107])).
% 3.80/2.00  tff(c_28, plain, (![C_18, A_16, B_17]: (m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~r1_tarski(k2_relat_1(C_18), B_17) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.80/2.00  tff(c_297, plain, (![B_72, C_73, A_74]: (k1_xboole_0=B_72 | v1_funct_2(C_73, A_74, B_72) | k1_relset_1(A_74, B_72, C_73)!=A_74 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_72))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.80/2.00  tff(c_400, plain, (![B_91, C_92, A_93]: (k1_xboole_0=B_91 | v1_funct_2(C_92, A_93, B_91) | k1_relset_1(A_93, B_91, C_92)!=A_93 | ~r1_tarski(k2_relat_1(C_92), B_91) | ~r1_tarski(k1_relat_1(C_92), A_93) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_28, c_297])).
% 3.80/2.00  tff(c_409, plain, (![C_94, A_95]: (k2_relat_1(C_94)=k1_xboole_0 | v1_funct_2(C_94, A_95, k2_relat_1(C_94)) | k1_relset_1(A_95, k2_relat_1(C_94), C_94)!=A_95 | ~r1_tarski(k1_relat_1(C_94), A_95) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_6, c_400])).
% 3.80/2.00  tff(c_44, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.80/2.00  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.80/2.00  tff(c_48, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 3.80/2.00  tff(c_71, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.80/2.00  tff(c_419, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_409, c_71])).
% 3.80/2.00  tff(c_429, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_419])).
% 3.80/2.00  tff(c_430, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_108, c_429])).
% 3.80/2.00  tff(c_435, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_345, c_430])).
% 3.80/2.00  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_435])).
% 3.80/2.00  tff(c_440, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_107])).
% 3.80/2.00  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.80/2.00  tff(c_450, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_440, c_440, c_20])).
% 3.80/2.00  tff(c_89, plain, (![A_31]: (k1_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/2.00  tff(c_97, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_89])).
% 3.80/2.00  tff(c_98, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_97])).
% 3.80/2.00  tff(c_442, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_440, c_98])).
% 3.80/2.00  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_450, c_442])).
% 3.80/2.00  tff(c_468, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_97])).
% 3.80/2.00  tff(c_469, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_97])).
% 3.80/2.00  tff(c_491, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_468, c_469])).
% 3.80/2.00  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/2.00  tff(c_484, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_10])).
% 3.80/2.00  tff(c_609, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/2.00  tff(c_616, plain, (![A_115, B_116]: (k1_relset_1(A_115, B_116, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_484, c_609])).
% 3.80/2.00  tff(c_618, plain, (![A_115, B_116]: (k1_relset_1(A_115, B_116, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_616])).
% 3.80/2.00  tff(c_72, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_28, B_29)), A_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/2.00  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/2.00  tff(c_77, plain, (![B_29]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_29))=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_8])).
% 3.80/2.00  tff(c_481, plain, (![B_29]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_29))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_468, c_77])).
% 3.80/2.00  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/2.00  tff(c_96, plain, (![A_8, B_9]: (k1_relat_1(k2_zfmisc_1(A_8, B_9))!=k1_xboole_0 | k2_zfmisc_1(A_8, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_89])).
% 3.80/2.00  tff(c_576, plain, (![A_110, B_111]: (k1_relat_1(k2_zfmisc_1(A_110, B_111))!='#skF_1' | k2_zfmisc_1(A_110, B_111)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_468, c_96])).
% 3.80/2.00  tff(c_580, plain, (![B_29]: (k2_zfmisc_1('#skF_1', B_29)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_481, c_576])).
% 3.80/2.00  tff(c_34, plain, (![C_21, B_20]: (v1_funct_2(C_21, k1_xboole_0, B_20) | k1_relset_1(k1_xboole_0, B_20, C_21)!=k1_xboole_0 | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.80/2.00  tff(c_652, plain, (![C_126, B_127]: (v1_funct_2(C_126, '#skF_1', B_127) | k1_relset_1('#skF_1', B_127, C_126)!='#skF_1' | ~m1_subset_1(C_126, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_468, c_468, c_468, c_468, c_34])).
% 3.80/2.00  tff(c_655, plain, (![B_127]: (v1_funct_2('#skF_1', '#skF_1', B_127) | k1_relset_1('#skF_1', B_127, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_484, c_652])).
% 3.80/2.00  tff(c_658, plain, (![B_127]: (v1_funct_2('#skF_1', '#skF_1', B_127))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_655])).
% 3.80/2.00  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.80/2.00  tff(c_485, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_468, c_468, c_18])).
% 3.80/2.00  tff(c_492, plain, (~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_71])).
% 3.80/2.00  tff(c_516, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_492])).
% 3.80/2.00  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_658, c_516])).
% 3.80/2.00  tff(c_662, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_48])).
% 3.80/2.00  tff(c_837, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_825, c_662])).
% 3.80/2.00  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_6, c_837])).
% 3.80/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/2.00  
% 3.80/2.00  Inference rules
% 3.80/2.00  ----------------------
% 3.80/2.00  #Ref     : 0
% 3.80/2.00  #Sup     : 156
% 3.80/2.00  #Fact    : 0
% 3.80/2.00  #Define  : 0
% 3.80/2.00  #Split   : 5
% 3.80/2.00  #Chain   : 0
% 3.80/2.00  #Close   : 0
% 3.80/2.00  
% 3.80/2.00  Ordering : KBO
% 3.80/2.00  
% 3.80/2.00  Simplification rules
% 3.80/2.00  ----------------------
% 3.80/2.00  #Subsume      : 7
% 3.80/2.00  #Demod        : 202
% 3.80/2.00  #Tautology    : 105
% 3.80/2.00  #SimpNegUnit  : 1
% 3.80/2.00  #BackRed      : 23
% 3.80/2.00  
% 3.80/2.00  #Partial instantiations: 0
% 3.80/2.00  #Strategies tried      : 1
% 3.80/2.00  
% 3.80/2.00  Timing (in seconds)
% 3.80/2.00  ----------------------
% 3.80/2.01  Preprocessing        : 0.49
% 3.80/2.01  Parsing              : 0.25
% 3.80/2.01  CNF conversion       : 0.03
% 3.80/2.01  Main loop            : 0.55
% 3.80/2.01  Inferencing          : 0.20
% 3.80/2.01  Reduction            : 0.17
% 3.80/2.01  Demodulation         : 0.12
% 3.80/2.01  BG Simplification    : 0.03
% 3.80/2.01  Subsumption          : 0.11
% 3.80/2.01  Abstraction          : 0.03
% 3.80/2.01  MUC search           : 0.00
% 3.80/2.01  Cooper               : 0.00
% 3.80/2.01  Total                : 1.10
% 3.80/2.01  Index Insertion      : 0.00
% 3.80/2.01  Index Deletion       : 0.00
% 3.80/2.01  Index Matching       : 0.00
% 3.80/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
