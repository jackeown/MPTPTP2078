%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:16 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 364 expanded)
%              Number of leaves         :   41 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  147 ( 726 expanded)
%              Number of equality atoms :   34 ( 119 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_34,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_95,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_101,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_105,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_133,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_289,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_308,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_289])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_168,plain,(
    ! [A_96,C_97,B_98] :
      ( m1_subset_1(A_96,C_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(C_97))
      | ~ r2_hidden(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_176,plain,(
    ! [A_100,B_101,A_102] :
      ( m1_subset_1(A_100,B_101)
      | ~ r2_hidden(A_100,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_12,c_168])).

tff(c_183,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1('#skF_1'(A_103),B_104)
      | ~ r1_tarski(A_103,B_104)
      | v1_xboole_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_74,plain,(
    ! [A_67] :
      ( v1_xboole_0(A_67)
      | r2_hidden('#skF_1'(A_67),A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,k2_relset_1('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(D_59,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_7','#skF_8','#skF_9')),'#skF_8')
    | v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_74,c_46])).

tff(c_167,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_7','#skF_8','#skF_9')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_207,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_183,c_167])).

tff(c_266,plain,(
    ~ r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_309,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_266])).

tff(c_319,plain,
    ( ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_309])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_133,c_319])).

tff(c_324,plain,(
    v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_57,plain,(
    ! [A_64] :
      ( r2_hidden('#skF_2'(A_64),A_64)
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(A_64)
      | k1_xboole_0 = A_64 ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_329,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_324,c_61])).

tff(c_356,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_371,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_356])).

tff(c_376,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_371])).

tff(c_36,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(k2_relat_1(A_38))
      | ~ v1_relat_1(A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_386,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_36])).

tff(c_394,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_6,c_386])).

tff(c_399,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_394,c_61])).

tff(c_212,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_226,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_212])).

tff(c_48,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_227,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_48])).

tff(c_419,plain,(
    k1_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_227])).

tff(c_458,plain,(
    ! [C_121,A_122] :
      ( r2_hidden(k4_tarski(C_121,'#skF_6'(A_122,k1_relat_1(A_122),C_121)),A_122)
      | ~ r2_hidden(C_121,k1_relat_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_492,plain,(
    ! [A_125,C_126] :
      ( ~ v1_xboole_0(A_125)
      | ~ r2_hidden(C_126,k1_relat_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_458,c_2])).

tff(c_503,plain,(
    ! [A_127] :
      ( ~ v1_xboole_0(A_127)
      | v1_xboole_0(k1_relat_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_4,c_492])).

tff(c_420,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(A_64)
      | A_64 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_61])).

tff(c_508,plain,(
    ! [A_128] :
      ( k1_relat_1(A_128) = '#skF_9'
      | ~ v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_503,c_420])).

tff(c_514,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_394,c_508])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_514])).

tff(c_520,plain,(
    v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_525,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_520,c_61])).

tff(c_649,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relset_1(A_146,B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_664,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_649])).

tff(c_669,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_664])).

tff(c_679,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_36])).

tff(c_687,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_6,c_679])).

tff(c_692,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_687,c_61])).

tff(c_624,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_643,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_624])).

tff(c_644,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_48])).

tff(c_694,plain,(
    k1_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_644])).

tff(c_727,plain,(
    ! [C_149,A_150] :
      ( r2_hidden(k4_tarski(C_149,'#skF_6'(A_150,k1_relat_1(A_150),C_149)),A_150)
      | ~ r2_hidden(C_149,k1_relat_1(A_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_762,plain,(
    ! [A_153,C_154] :
      ( ~ v1_xboole_0(A_153)
      | ~ r2_hidden(C_154,k1_relat_1(A_153)) ) ),
    inference(resolution,[status(thm)],[c_727,c_2])).

tff(c_773,plain,(
    ! [A_155] :
      ( ~ v1_xboole_0(A_155)
      | v1_xboole_0(k1_relat_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_4,c_762])).

tff(c_700,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(A_64)
      | A_64 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_61])).

tff(c_778,plain,(
    ! [A_156] :
      ( k1_relat_1(A_156) = '#skF_9'
      | ~ v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_773,c_700])).

tff(c_784,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_687,c_778])).

tff(c_789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_694,c_784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 2.76/1.42  
% 2.76/1.42  %Foreground sorts:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Background operators:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Foreground operators:
% 2.76/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.76/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.76/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.76/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.76/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.76/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.76/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.76/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.42  
% 3.10/1.44  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.10/1.44  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.10/1.44  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.10/1.44  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.10/1.44  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.44  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.10/1.44  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.10/1.44  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.44  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.10/1.44  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.10/1.44  tff(f_81, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.10/1.44  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.10/1.44  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.10/1.44  tff(c_34, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.10/1.44  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.10/1.44  tff(c_95, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.44  tff(c_101, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_95])).
% 3.10/1.44  tff(c_105, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_101])).
% 3.10/1.44  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.44  tff(c_124, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.10/1.44  tff(c_133, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_124])).
% 3.10/1.44  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.10/1.44  tff(c_289, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.10/1.44  tff(c_308, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_289])).
% 3.10/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.44  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.10/1.44  tff(c_168, plain, (![A_96, C_97, B_98]: (m1_subset_1(A_96, C_97) | ~m1_subset_1(B_98, k1_zfmisc_1(C_97)) | ~r2_hidden(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.10/1.44  tff(c_176, plain, (![A_100, B_101, A_102]: (m1_subset_1(A_100, B_101) | ~r2_hidden(A_100, A_102) | ~r1_tarski(A_102, B_101))), inference(resolution, [status(thm)], [c_12, c_168])).
% 3.10/1.44  tff(c_183, plain, (![A_103, B_104]: (m1_subset_1('#skF_1'(A_103), B_104) | ~r1_tarski(A_103, B_104) | v1_xboole_0(A_103))), inference(resolution, [status(thm)], [c_4, c_176])).
% 3.10/1.44  tff(c_74, plain, (![A_67]: (v1_xboole_0(A_67) | r2_hidden('#skF_1'(A_67), A_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.44  tff(c_46, plain, (![D_59]: (~r2_hidden(D_59, k2_relset_1('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(D_59, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.10/1.44  tff(c_82, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_7', '#skF_8', '#skF_9')), '#skF_8') | v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_74, c_46])).
% 3.10/1.44  tff(c_167, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_7', '#skF_8', '#skF_9')), '#skF_8')), inference(splitLeft, [status(thm)], [c_82])).
% 3.10/1.44  tff(c_207, plain, (~r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_183, c_167])).
% 3.10/1.44  tff(c_266, plain, (~r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_207])).
% 3.10/1.44  tff(c_309, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_266])).
% 3.10/1.44  tff(c_319, plain, (~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20, c_309])).
% 3.10/1.44  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_133, c_319])).
% 3.10/1.44  tff(c_324, plain, (v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_207])).
% 3.10/1.44  tff(c_57, plain, (![A_64]: (r2_hidden('#skF_2'(A_64), A_64) | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.10/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.44  tff(c_61, plain, (![A_64]: (~v1_xboole_0(A_64) | k1_xboole_0=A_64)), inference(resolution, [status(thm)], [c_57, c_2])).
% 3.10/1.44  tff(c_329, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_324, c_61])).
% 3.10/1.44  tff(c_356, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.10/1.44  tff(c_371, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_356])).
% 3.10/1.44  tff(c_376, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_329, c_371])).
% 3.10/1.44  tff(c_36, plain, (![A_38]: (~v1_xboole_0(k2_relat_1(A_38)) | ~v1_relat_1(A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.44  tff(c_386, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_9') | v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_376, c_36])).
% 3.10/1.44  tff(c_394, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_6, c_386])).
% 3.10/1.44  tff(c_399, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_394, c_61])).
% 3.10/1.44  tff(c_212, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.10/1.44  tff(c_226, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_212])).
% 3.10/1.44  tff(c_48, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.10/1.44  tff(c_227, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_226, c_48])).
% 3.10/1.44  tff(c_419, plain, (k1_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_399, c_227])).
% 3.10/1.44  tff(c_458, plain, (![C_121, A_122]: (r2_hidden(k4_tarski(C_121, '#skF_6'(A_122, k1_relat_1(A_122), C_121)), A_122) | ~r2_hidden(C_121, k1_relat_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.44  tff(c_492, plain, (![A_125, C_126]: (~v1_xboole_0(A_125) | ~r2_hidden(C_126, k1_relat_1(A_125)))), inference(resolution, [status(thm)], [c_458, c_2])).
% 3.10/1.44  tff(c_503, plain, (![A_127]: (~v1_xboole_0(A_127) | v1_xboole_0(k1_relat_1(A_127)))), inference(resolution, [status(thm)], [c_4, c_492])).
% 3.10/1.44  tff(c_420, plain, (![A_64]: (~v1_xboole_0(A_64) | A_64='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_61])).
% 3.10/1.44  tff(c_508, plain, (![A_128]: (k1_relat_1(A_128)='#skF_9' | ~v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_503, c_420])).
% 3.10/1.44  tff(c_514, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_394, c_508])).
% 3.10/1.44  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_514])).
% 3.10/1.44  tff(c_520, plain, (v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_82])).
% 3.10/1.44  tff(c_525, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_520, c_61])).
% 3.10/1.44  tff(c_649, plain, (![A_146, B_147, C_148]: (k2_relset_1(A_146, B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.10/1.44  tff(c_664, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_649])).
% 3.10/1.44  tff(c_669, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_525, c_664])).
% 3.10/1.44  tff(c_679, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_9') | v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_669, c_36])).
% 3.10/1.44  tff(c_687, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_6, c_679])).
% 3.10/1.44  tff(c_692, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_687, c_61])).
% 3.10/1.44  tff(c_624, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.10/1.44  tff(c_643, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_624])).
% 3.10/1.44  tff(c_644, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_643, c_48])).
% 3.10/1.44  tff(c_694, plain, (k1_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_692, c_644])).
% 3.10/1.44  tff(c_727, plain, (![C_149, A_150]: (r2_hidden(k4_tarski(C_149, '#skF_6'(A_150, k1_relat_1(A_150), C_149)), A_150) | ~r2_hidden(C_149, k1_relat_1(A_150)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.44  tff(c_762, plain, (![A_153, C_154]: (~v1_xboole_0(A_153) | ~r2_hidden(C_154, k1_relat_1(A_153)))), inference(resolution, [status(thm)], [c_727, c_2])).
% 3.10/1.44  tff(c_773, plain, (![A_155]: (~v1_xboole_0(A_155) | v1_xboole_0(k1_relat_1(A_155)))), inference(resolution, [status(thm)], [c_4, c_762])).
% 3.10/1.44  tff(c_700, plain, (![A_64]: (~v1_xboole_0(A_64) | A_64='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_61])).
% 3.10/1.44  tff(c_778, plain, (![A_156]: (k1_relat_1(A_156)='#skF_9' | ~v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_773, c_700])).
% 3.10/1.44  tff(c_784, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_687, c_778])).
% 3.10/1.44  tff(c_789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_694, c_784])).
% 3.10/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.44  
% 3.10/1.44  Inference rules
% 3.10/1.44  ----------------------
% 3.10/1.44  #Ref     : 0
% 3.10/1.44  #Sup     : 150
% 3.10/1.44  #Fact    : 0
% 3.10/1.44  #Define  : 0
% 3.10/1.44  #Split   : 7
% 3.10/1.44  #Chain   : 0
% 3.10/1.44  #Close   : 0
% 3.10/1.44  
% 3.10/1.44  Ordering : KBO
% 3.10/1.44  
% 3.10/1.44  Simplification rules
% 3.10/1.44  ----------------------
% 3.10/1.44  #Subsume      : 5
% 3.10/1.44  #Demod        : 78
% 3.10/1.44  #Tautology    : 49
% 3.10/1.44  #SimpNegUnit  : 2
% 3.10/1.44  #BackRed      : 34
% 3.10/1.44  
% 3.10/1.44  #Partial instantiations: 0
% 3.10/1.44  #Strategies tried      : 1
% 3.10/1.44  
% 3.10/1.44  Timing (in seconds)
% 3.10/1.44  ----------------------
% 3.10/1.44  Preprocessing        : 0.33
% 3.10/1.44  Parsing              : 0.17
% 3.10/1.44  CNF conversion       : 0.03
% 3.10/1.44  Main loop            : 0.33
% 3.10/1.44  Inferencing          : 0.12
% 3.10/1.44  Reduction            : 0.10
% 3.10/1.44  Demodulation         : 0.07
% 3.10/1.44  BG Simplification    : 0.02
% 3.10/1.44  Subsumption          : 0.05
% 3.10/1.44  Abstraction          : 0.02
% 3.10/1.44  MUC search           : 0.00
% 3.10/1.44  Cooper               : 0.00
% 3.10/1.44  Total                : 0.71
% 3.10/1.44  Index Insertion      : 0.00
% 3.10/1.44  Index Deletion       : 0.00
% 3.10/1.44  Index Matching       : 0.00
% 3.10/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
