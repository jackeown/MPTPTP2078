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
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 307 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 618 expanded)
%              Number of equality atoms :   31 ( 102 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_111,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_638,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_647,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_638])).

tff(c_92,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_101,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_320,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_339,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_320])).

tff(c_125,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

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

tff(c_162,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_170,plain,(
    ! [A_98,B_99,A_100] :
      ( m1_subset_1(A_98,B_99)
      | ~ r2_hidden(A_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_12,c_162])).

tff(c_175,plain,(
    ! [A_1,B_99] :
      ( m1_subset_1('#skF_1'(A_1),B_99)
      | ~ r1_tarski(A_1,B_99)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_249,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_268,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_249])).

tff(c_70,plain,(
    ! [D_63] :
      ( ~ r2_hidden(D_63,k2_relset_1('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(D_63,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_79,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_7','#skF_8','#skF_9')),'#skF_8')
    | v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_177,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_7','#skF_8','#skF_9')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_269,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_9')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_177])).

tff(c_278,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_175,c_269])).

tff(c_296,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_299,plain,
    ( ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_134,c_299])).

tff(c_304,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_32,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(k2_relat_1(A_33))
      | ~ v1_relat_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_308,plain,
    ( ~ v1_relat_1('#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_304,c_32])).

tff(c_314,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_308])).

tff(c_54,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_2'(A_60),A_60)
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(A_60)
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_319,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_314,c_58])).

tff(c_46,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_343,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_46])).

tff(c_393,plain,(
    k1_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_343])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_342,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_8])).

tff(c_482,plain,(
    ! [C_126,A_127] :
      ( r2_hidden(k4_tarski(C_126,'#skF_6'(A_127,k1_relat_1(A_127),C_126)),A_127)
      | ~ r2_hidden(C_126,k1_relat_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_499,plain,(
    ! [A_128,C_129] :
      ( ~ v1_xboole_0(A_128)
      | ~ r2_hidden(C_129,k1_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_482,c_2])).

tff(c_520,plain,(
    ! [A_131] :
      ( ~ v1_xboole_0(A_131)
      | k1_relat_1(A_131) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_342,c_499])).

tff(c_526,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_314,c_520])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_526])).

tff(c_532,plain,(
    v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_538,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_532,c_58])).

tff(c_561,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_568,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_561])).

tff(c_571,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_568])).

tff(c_581,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_32])).

tff(c_589,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_6,c_581])).

tff(c_594,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_589,c_58])).

tff(c_602,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_46])).

tff(c_648,plain,(
    k1_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_602])).

tff(c_601,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_8])).

tff(c_765,plain,(
    ! [C_150,A_151] :
      ( r2_hidden(k4_tarski(C_150,'#skF_6'(A_151,k1_relat_1(A_151),C_150)),A_151)
      | ~ r2_hidden(C_150,k1_relat_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_782,plain,(
    ! [A_152,C_153] :
      ( ~ v1_xboole_0(A_152)
      | ~ r2_hidden(C_153,k1_relat_1(A_152)) ) ),
    inference(resolution,[status(thm)],[c_765,c_2])).

tff(c_803,plain,(
    ! [A_155] :
      ( ~ v1_xboole_0(A_155)
      | k1_relat_1(A_155) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_601,c_782])).

tff(c_809,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_589,c_803])).

tff(c_814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 2.86/1.42  
% 2.86/1.42  %Foreground sorts:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Background operators:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Foreground operators:
% 2.86/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.86/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.86/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.86/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.86/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.42  
% 2.86/1.43  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.86/1.43  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.86/1.43  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.86/1.43  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.86/1.43  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.43  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.86/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.86/1.43  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.43  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.86/1.43  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.86/1.43  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.86/1.43  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.86/1.43  tff(f_64, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.86/1.43  tff(c_48, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.86/1.43  tff(c_638, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.86/1.43  tff(c_647, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_638])).
% 2.86/1.43  tff(c_92, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.86/1.43  tff(c_101, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_92])).
% 2.86/1.43  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.43  tff(c_320, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.86/1.43  tff(c_339, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_320])).
% 2.86/1.43  tff(c_125, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.43  tff(c_134, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_125])).
% 2.86/1.43  tff(c_18, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.43  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.43  tff(c_162, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.43  tff(c_170, plain, (![A_98, B_99, A_100]: (m1_subset_1(A_98, B_99) | ~r2_hidden(A_98, A_100) | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_12, c_162])).
% 2.86/1.43  tff(c_175, plain, (![A_1, B_99]: (m1_subset_1('#skF_1'(A_1), B_99) | ~r1_tarski(A_1, B_99) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_170])).
% 2.86/1.43  tff(c_249, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.43  tff(c_268, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_249])).
% 2.86/1.43  tff(c_70, plain, (![D_63]: (~r2_hidden(D_63, k2_relset_1('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(D_63, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.86/1.43  tff(c_79, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_7', '#skF_8', '#skF_9')), '#skF_8') | v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_4, c_70])).
% 2.86/1.43  tff(c_177, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_7', '#skF_8', '#skF_9')), '#skF_8')), inference(splitLeft, [status(thm)], [c_79])).
% 2.86/1.43  tff(c_269, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_9')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_177])).
% 2.86/1.43  tff(c_278, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_175, c_269])).
% 2.86/1.43  tff(c_296, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_278])).
% 2.86/1.43  tff(c_299, plain, (~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_18, c_296])).
% 2.86/1.43  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_134, c_299])).
% 2.86/1.43  tff(c_304, plain, (v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_278])).
% 2.86/1.43  tff(c_32, plain, (![A_33]: (~v1_xboole_0(k2_relat_1(A_33)) | ~v1_relat_1(A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.43  tff(c_308, plain, (~v1_relat_1('#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_304, c_32])).
% 2.86/1.43  tff(c_314, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_308])).
% 2.86/1.43  tff(c_54, plain, (![A_60]: (r2_hidden('#skF_2'(A_60), A_60) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.43  tff(c_58, plain, (![A_60]: (~v1_xboole_0(A_60) | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.86/1.43  tff(c_319, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_314, c_58])).
% 2.86/1.43  tff(c_46, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.86/1.43  tff(c_343, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_319, c_46])).
% 2.86/1.43  tff(c_393, plain, (k1_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_339, c_343])).
% 2.86/1.43  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.43  tff(c_342, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_8])).
% 2.86/1.43  tff(c_482, plain, (![C_126, A_127]: (r2_hidden(k4_tarski(C_126, '#skF_6'(A_127, k1_relat_1(A_127), C_126)), A_127) | ~r2_hidden(C_126, k1_relat_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.43  tff(c_499, plain, (![A_128, C_129]: (~v1_xboole_0(A_128) | ~r2_hidden(C_129, k1_relat_1(A_128)))), inference(resolution, [status(thm)], [c_482, c_2])).
% 2.86/1.43  tff(c_520, plain, (![A_131]: (~v1_xboole_0(A_131) | k1_relat_1(A_131)='#skF_9')), inference(resolution, [status(thm)], [c_342, c_499])).
% 2.86/1.43  tff(c_526, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_314, c_520])).
% 2.86/1.43  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_393, c_526])).
% 2.86/1.43  tff(c_532, plain, (v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_79])).
% 2.86/1.43  tff(c_538, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_532, c_58])).
% 2.86/1.43  tff(c_561, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.43  tff(c_568, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_561])).
% 2.86/1.43  tff(c_571, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_538, c_568])).
% 2.86/1.43  tff(c_581, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_9') | v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_571, c_32])).
% 2.86/1.43  tff(c_589, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_6, c_581])).
% 2.86/1.43  tff(c_594, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_589, c_58])).
% 2.86/1.43  tff(c_602, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_594, c_46])).
% 2.86/1.43  tff(c_648, plain, (k1_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_602])).
% 2.86/1.43  tff(c_601, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_8])).
% 2.86/1.43  tff(c_765, plain, (![C_150, A_151]: (r2_hidden(k4_tarski(C_150, '#skF_6'(A_151, k1_relat_1(A_151), C_150)), A_151) | ~r2_hidden(C_150, k1_relat_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.43  tff(c_782, plain, (![A_152, C_153]: (~v1_xboole_0(A_152) | ~r2_hidden(C_153, k1_relat_1(A_152)))), inference(resolution, [status(thm)], [c_765, c_2])).
% 2.86/1.43  tff(c_803, plain, (![A_155]: (~v1_xboole_0(A_155) | k1_relat_1(A_155)='#skF_9')), inference(resolution, [status(thm)], [c_601, c_782])).
% 2.86/1.43  tff(c_809, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_589, c_803])).
% 2.86/1.43  tff(c_814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_648, c_809])).
% 2.86/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.43  
% 2.86/1.43  Inference rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Ref     : 0
% 2.86/1.43  #Sup     : 152
% 2.86/1.43  #Fact    : 0
% 2.86/1.43  #Define  : 0
% 2.86/1.43  #Split   : 4
% 2.86/1.43  #Chain   : 0
% 2.86/1.43  #Close   : 0
% 2.86/1.43  
% 2.86/1.43  Ordering : KBO
% 2.86/1.43  
% 2.86/1.43  Simplification rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Subsume      : 11
% 2.86/1.43  #Demod        : 78
% 2.86/1.43  #Tautology    : 50
% 2.86/1.43  #SimpNegUnit  : 2
% 2.86/1.43  #BackRed      : 25
% 2.86/1.43  
% 2.86/1.43  #Partial instantiations: 0
% 2.86/1.43  #Strategies tried      : 1
% 2.86/1.43  
% 2.86/1.43  Timing (in seconds)
% 2.86/1.43  ----------------------
% 2.86/1.44  Preprocessing        : 0.33
% 2.86/1.44  Parsing              : 0.17
% 2.86/1.44  CNF conversion       : 0.03
% 2.86/1.44  Main loop            : 0.34
% 2.86/1.44  Inferencing          : 0.13
% 2.86/1.44  Reduction            : 0.10
% 2.86/1.44  Demodulation         : 0.07
% 2.86/1.44  BG Simplification    : 0.02
% 2.86/1.44  Subsumption          : 0.06
% 2.86/1.44  Abstraction          : 0.02
% 2.86/1.44  MUC search           : 0.00
% 2.86/1.44  Cooper               : 0.00
% 2.86/1.44  Total                : 0.70
% 2.86/1.44  Index Insertion      : 0.00
% 2.86/1.44  Index Deletion       : 0.00
% 2.86/1.44  Index Matching       : 0.00
% 2.86/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
