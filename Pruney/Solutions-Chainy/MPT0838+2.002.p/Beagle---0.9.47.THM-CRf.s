%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 448 expanded)
%              Number of leaves         :   35 ( 161 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 907 expanded)
%              Number of equality atoms :   31 ( 137 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1753,plain,(
    ! [A_246,B_247,C_248] :
      ( k1_relset_1(A_246,B_247,C_248) = k1_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1779,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1753])).

tff(c_38,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1780,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_38])).

tff(c_174,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_183,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_174])).

tff(c_291,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_310,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_291])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_376,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_395,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_376])).

tff(c_22,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,(
    ! [A_50,B_51] :
      ( v1_xboole_0(k2_zfmisc_1(A_50,B_51))
      | ~ v1_xboole_0(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_53,B_54] :
      ( k2_zfmisc_1(A_53,B_54) = k1_xboole_0
      | ~ v1_xboole_0(B_54) ) ),
    inference(resolution,[status(thm)],[c_58,c_12])).

tff(c_102,plain,(
    ! [A_57,A_58] :
      ( k2_zfmisc_1(A_57,k1_relat_1(A_58)) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_xboole_0(k2_zfmisc_1(A_11,B_12))
      | ~ v1_xboole_0(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    ! [A_58] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_14])).

tff(c_140,plain,(
    ! [A_63] :
      ( ~ v1_xboole_0(k1_relat_1(A_63))
      | ~ v1_xboole_0(A_63) ) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_150,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(resolution,[status(thm)],[c_22,c_140])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_4])).

tff(c_212,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_219,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83),B_84)
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_158,c_212])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_232,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_219,c_16])).

tff(c_162,plain,(
    ! [A_66] : r2_hidden('#skF_1'(A_66),A_66) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_4])).

tff(c_36,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_170,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_36])).

tff(c_241,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_232,c_170])).

tff(c_398,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_241])).

tff(c_408,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_398])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_310,c_408])).

tff(c_413,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_489,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_502,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_489])).

tff(c_66,plain,(
    ! [A_50,B_51] :
      ( k2_zfmisc_1(A_50,B_51) = k1_xboole_0
      | ~ v1_xboole_0(B_51) ) ),
    inference(resolution,[status(thm)],[c_58,c_12])).

tff(c_422,plain,(
    ! [A_50] : k2_zfmisc_1(A_50,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_413,c_66])).

tff(c_648,plain,(
    ! [C_153,B_154,A_155] :
      ( v5_relat_1(C_153,B_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_674,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_648])).

tff(c_611,plain,(
    ! [C_145,B_146,A_147] :
      ( r2_hidden(C_145,B_146)
      | ~ r2_hidden(C_145,A_147)
      | ~ r1_tarski(A_147,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_966,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173),B_174)
      | ~ r1_tarski(A_173,B_174)
      | v1_xboole_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_4,c_611])).

tff(c_1072,plain,(
    ! [A_182,B_183] :
      ( m1_subset_1('#skF_1'(A_182),B_183)
      | ~ r1_tarski(A_182,B_183)
      | v1_xboole_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_966,c_16])).

tff(c_983,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relset_1(A_175,B_176,C_177) = k2_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1009,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_983])).

tff(c_426,plain,(
    ! [D_119] :
      ( ~ r2_hidden(D_119,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_119,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_431,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_426])).

tff(c_505,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_1011,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_505])).

tff(c_1096,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1072,c_1011])).

tff(c_1102,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1096])).

tff(c_1105,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_1102])).

tff(c_1112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_674,c_1105])).

tff(c_1113,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_1130,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1113,c_12])).

tff(c_24,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1174,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_24])).

tff(c_1189,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_422,c_1174])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_982,plain,(
    ! [B_174,A_173] :
      ( ~ v1_xboole_0(B_174)
      | ~ r1_tarski(A_173,B_174)
      | v1_xboole_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_966,c_2])).

tff(c_1201,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1189,c_982])).

tff(c_1204,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_1201])).

tff(c_1220,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1204,c_12])).

tff(c_1131,plain,(
    ! [A_184,B_185,C_186] :
      ( k1_relset_1(A_184,B_185,C_186) = k1_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1162,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1131])).

tff(c_1205,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_38])).

tff(c_1247,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1205])).

tff(c_47,plain,(
    ! [A_46] :
      ( v1_xboole_0(k1_relat_1(A_46))
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_51,plain,(
    ! [A_46] :
      ( k1_relat_1(A_46) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_47,c_12])).

tff(c_1219,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1204,c_51])).

tff(c_1255,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1219])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1247,c_1255])).

tff(c_1257,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_1270,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1257,c_12])).

tff(c_1802,plain,(
    ! [A_251,B_252,C_253] :
      ( k2_relset_1(A_251,B_252,C_253) = k2_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1822,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1802])).

tff(c_1829,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_1822])).

tff(c_1841,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1829,c_24])).

tff(c_1854,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_422,c_1841])).

tff(c_1389,plain,(
    ! [C_202,B_203,A_204] :
      ( r2_hidden(C_202,B_203)
      | ~ r2_hidden(C_202,A_204)
      | ~ r1_tarski(A_204,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1785,plain,(
    ! [A_249,B_250] :
      ( r2_hidden('#skF_1'(A_249),B_250)
      | ~ r1_tarski(A_249,B_250)
      | v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_4,c_1389])).

tff(c_1887,plain,(
    ! [B_257,A_258] :
      ( ~ v1_xboole_0(B_257)
      | ~ r1_tarski(A_258,B_257)
      | v1_xboole_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_1785,c_2])).

tff(c_1893,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1854,c_1887])).

tff(c_1910,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_1893])).

tff(c_1941,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1910,c_51])).

tff(c_1949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1780,c_1941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.66  
% 3.59/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.66  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.59/1.66  
% 3.59/1.66  %Foreground sorts:
% 3.59/1.66  
% 3.59/1.66  
% 3.59/1.66  %Background operators:
% 3.59/1.66  
% 3.59/1.66  
% 3.59/1.66  %Foreground operators:
% 3.59/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.59/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.59/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.59/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.59/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.59/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.66  
% 3.59/1.68  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.59/1.68  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.59/1.68  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.59/1.68  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.59/1.68  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.59/1.68  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.59/1.68  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.59/1.68  tff(f_46, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.59/1.68  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.59/1.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.59/1.68  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.59/1.68  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.59/1.68  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.59/1.68  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.59/1.68  tff(c_1753, plain, (![A_246, B_247, C_248]: (k1_relset_1(A_246, B_247, C_248)=k1_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.59/1.68  tff(c_1779, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1753])).
% 3.59/1.68  tff(c_38, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.59/1.68  tff(c_1780, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_38])).
% 3.59/1.68  tff(c_174, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.59/1.68  tff(c_183, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_174])).
% 3.59/1.68  tff(c_291, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.59/1.68  tff(c_310, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_291])).
% 3.59/1.68  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.59/1.68  tff(c_376, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.59/1.68  tff(c_395, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_376])).
% 3.59/1.68  tff(c_22, plain, (![A_17]: (v1_xboole_0(k1_relat_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.59/1.68  tff(c_58, plain, (![A_50, B_51]: (v1_xboole_0(k2_zfmisc_1(A_50, B_51)) | ~v1_xboole_0(B_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.59/1.68  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.59/1.68  tff(c_76, plain, (![A_53, B_54]: (k2_zfmisc_1(A_53, B_54)=k1_xboole_0 | ~v1_xboole_0(B_54))), inference(resolution, [status(thm)], [c_58, c_12])).
% 3.59/1.68  tff(c_102, plain, (![A_57, A_58]: (k2_zfmisc_1(A_57, k1_relat_1(A_58))=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_22, c_76])).
% 3.59/1.68  tff(c_14, plain, (![A_11, B_12]: (v1_xboole_0(k2_zfmisc_1(A_11, B_12)) | ~v1_xboole_0(B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.59/1.68  tff(c_108, plain, (![A_58]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_58)) | ~v1_xboole_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_102, c_14])).
% 3.59/1.68  tff(c_140, plain, (![A_63]: (~v1_xboole_0(k1_relat_1(A_63)) | ~v1_xboole_0(A_63))), inference(splitLeft, [status(thm)], [c_108])).
% 3.59/1.68  tff(c_150, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_22, c_140])).
% 3.59/1.68  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.59/1.68  tff(c_158, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_150, c_4])).
% 3.59/1.68  tff(c_212, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.59/1.68  tff(c_219, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83), B_84) | ~r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_158, c_212])).
% 3.59/1.68  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.59/1.68  tff(c_232, plain, (![A_85, B_86]: (m1_subset_1('#skF_1'(A_85), B_86) | ~r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_219, c_16])).
% 3.59/1.68  tff(c_162, plain, (![A_66]: (r2_hidden('#skF_1'(A_66), A_66))), inference(negUnitSimplification, [status(thm)], [c_150, c_4])).
% 3.59/1.68  tff(c_36, plain, (![D_42]: (~r2_hidden(D_42, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.59/1.68  tff(c_170, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_162, c_36])).
% 3.59/1.68  tff(c_241, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_232, c_170])).
% 3.59/1.68  tff(c_398, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_241])).
% 3.59/1.68  tff(c_408, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_398])).
% 3.59/1.68  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_310, c_408])).
% 3.59/1.68  tff(c_413, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_108])).
% 3.59/1.68  tff(c_489, plain, (![C_123, A_124, B_125]: (v1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.59/1.68  tff(c_502, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_489])).
% 3.59/1.68  tff(c_66, plain, (![A_50, B_51]: (k2_zfmisc_1(A_50, B_51)=k1_xboole_0 | ~v1_xboole_0(B_51))), inference(resolution, [status(thm)], [c_58, c_12])).
% 3.59/1.68  tff(c_422, plain, (![A_50]: (k2_zfmisc_1(A_50, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_413, c_66])).
% 3.59/1.68  tff(c_648, plain, (![C_153, B_154, A_155]: (v5_relat_1(C_153, B_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.59/1.68  tff(c_674, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_648])).
% 3.59/1.68  tff(c_611, plain, (![C_145, B_146, A_147]: (r2_hidden(C_145, B_146) | ~r2_hidden(C_145, A_147) | ~r1_tarski(A_147, B_146))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.59/1.68  tff(c_966, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173), B_174) | ~r1_tarski(A_173, B_174) | v1_xboole_0(A_173))), inference(resolution, [status(thm)], [c_4, c_611])).
% 3.59/1.68  tff(c_1072, plain, (![A_182, B_183]: (m1_subset_1('#skF_1'(A_182), B_183) | ~r1_tarski(A_182, B_183) | v1_xboole_0(A_182))), inference(resolution, [status(thm)], [c_966, c_16])).
% 3.59/1.68  tff(c_983, plain, (![A_175, B_176, C_177]: (k2_relset_1(A_175, B_176, C_177)=k2_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.59/1.68  tff(c_1009, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_983])).
% 3.59/1.68  tff(c_426, plain, (![D_119]: (~r2_hidden(D_119, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_119, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.59/1.68  tff(c_431, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_426])).
% 3.59/1.68  tff(c_505, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_431])).
% 3.59/1.68  tff(c_1011, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_505])).
% 3.59/1.68  tff(c_1096, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1072, c_1011])).
% 3.59/1.68  tff(c_1102, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1096])).
% 3.59/1.68  tff(c_1105, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_1102])).
% 3.59/1.68  tff(c_1112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_502, c_674, c_1105])).
% 3.59/1.68  tff(c_1113, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1096])).
% 3.59/1.68  tff(c_1130, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1113, c_12])).
% 3.59/1.68  tff(c_24, plain, (![A_18]: (r1_tarski(A_18, k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.59/1.68  tff(c_1174, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0)) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1130, c_24])).
% 3.59/1.68  tff(c_1189, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_422, c_1174])).
% 3.59/1.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.59/1.68  tff(c_982, plain, (![B_174, A_173]: (~v1_xboole_0(B_174) | ~r1_tarski(A_173, B_174) | v1_xboole_0(A_173))), inference(resolution, [status(thm)], [c_966, c_2])).
% 3.59/1.68  tff(c_1201, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1189, c_982])).
% 3.59/1.68  tff(c_1204, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_1201])).
% 3.59/1.68  tff(c_1220, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1204, c_12])).
% 3.59/1.68  tff(c_1131, plain, (![A_184, B_185, C_186]: (k1_relset_1(A_184, B_185, C_186)=k1_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.59/1.68  tff(c_1162, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1131])).
% 3.59/1.68  tff(c_1205, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_38])).
% 3.59/1.68  tff(c_1247, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1205])).
% 3.59/1.68  tff(c_47, plain, (![A_46]: (v1_xboole_0(k1_relat_1(A_46)) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.59/1.68  tff(c_51, plain, (![A_46]: (k1_relat_1(A_46)=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_47, c_12])).
% 3.59/1.68  tff(c_1219, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1204, c_51])).
% 3.59/1.68  tff(c_1255, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1219])).
% 3.59/1.68  tff(c_1256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1247, c_1255])).
% 3.59/1.68  tff(c_1257, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_431])).
% 3.59/1.68  tff(c_1270, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1257, c_12])).
% 3.59/1.68  tff(c_1802, plain, (![A_251, B_252, C_253]: (k2_relset_1(A_251, B_252, C_253)=k2_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.59/1.68  tff(c_1822, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1802])).
% 3.59/1.68  tff(c_1829, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_1822])).
% 3.59/1.68  tff(c_1841, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0)) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1829, c_24])).
% 3.59/1.68  tff(c_1854, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_422, c_1841])).
% 3.59/1.68  tff(c_1389, plain, (![C_202, B_203, A_204]: (r2_hidden(C_202, B_203) | ~r2_hidden(C_202, A_204) | ~r1_tarski(A_204, B_203))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.59/1.68  tff(c_1785, plain, (![A_249, B_250]: (r2_hidden('#skF_1'(A_249), B_250) | ~r1_tarski(A_249, B_250) | v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_4, c_1389])).
% 3.59/1.68  tff(c_1887, plain, (![B_257, A_258]: (~v1_xboole_0(B_257) | ~r1_tarski(A_258, B_257) | v1_xboole_0(A_258))), inference(resolution, [status(thm)], [c_1785, c_2])).
% 3.59/1.68  tff(c_1893, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1854, c_1887])).
% 3.59/1.68  tff(c_1910, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_1893])).
% 3.59/1.68  tff(c_1941, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1910, c_51])).
% 3.59/1.68  tff(c_1949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1780, c_1941])).
% 3.59/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.68  
% 3.59/1.68  Inference rules
% 3.59/1.68  ----------------------
% 3.59/1.68  #Ref     : 0
% 3.59/1.68  #Sup     : 387
% 3.59/1.68  #Fact    : 0
% 3.59/1.68  #Define  : 0
% 3.59/1.68  #Split   : 8
% 3.59/1.68  #Chain   : 0
% 3.59/1.68  #Close   : 0
% 3.59/1.68  
% 3.59/1.68  Ordering : KBO
% 3.59/1.68  
% 3.59/1.68  Simplification rules
% 3.59/1.68  ----------------------
% 3.59/1.68  #Subsume      : 44
% 3.59/1.68  #Demod        : 303
% 3.59/1.68  #Tautology    : 134
% 3.59/1.68  #SimpNegUnit  : 11
% 3.59/1.68  #BackRed      : 95
% 3.59/1.68  
% 3.59/1.68  #Partial instantiations: 0
% 3.59/1.68  #Strategies tried      : 1
% 3.59/1.68  
% 3.59/1.68  Timing (in seconds)
% 3.59/1.68  ----------------------
% 3.76/1.68  Preprocessing        : 0.31
% 3.76/1.68  Parsing              : 0.16
% 3.76/1.68  CNF conversion       : 0.02
% 3.76/1.68  Main loop            : 0.52
% 3.76/1.68  Inferencing          : 0.19
% 3.76/1.68  Reduction            : 0.16
% 3.76/1.68  Demodulation         : 0.10
% 3.76/1.68  BG Simplification    : 0.03
% 3.76/1.68  Subsumption          : 0.09
% 3.76/1.68  Abstraction          : 0.03
% 3.76/1.69  MUC search           : 0.00
% 3.76/1.69  Cooper               : 0.00
% 3.76/1.69  Total                : 0.87
% 3.76/1.69  Index Insertion      : 0.00
% 3.76/1.69  Index Deletion       : 0.00
% 3.76/1.69  Index Matching       : 0.00
% 3.76/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
