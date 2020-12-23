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
% DateTime   : Thu Dec  3 10:08:10 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 285 expanded)
%              Number of leaves         :   38 ( 109 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 ( 557 expanded)
%              Number of equality atoms :   29 (  74 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2668,plain,(
    ! [A_345,B_346,C_347] :
      ( k1_relset_1(A_345,B_346,C_347) = k1_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2695,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2668])).

tff(c_42,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2697,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2695,c_42])).

tff(c_190,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_190])).

tff(c_219,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_232,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_219])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_20] :
      ( v1_xboole_0(k1_relat_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ! [A_54] :
      ( v1_xboole_0(k1_relat_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_93,plain,(
    ! [A_61] :
      ( k1_relat_1(k1_relat_1(A_61)) = k1_xboole_0
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_102,plain,(
    ! [A_61] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_26])).

tff(c_169,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k1_relat_1(A_72))
      | ~ v1_xboole_0(A_72) ) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_179,plain,(
    ! [A_20] : ~ v1_xboole_0(A_20) ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_4])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_304,plain,(
    ! [A_104,C_105,B_106] :
      ( m1_subset_1(A_104,C_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(C_105))
      | ~ r2_hidden(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_502,plain,(
    ! [A_135,B_136,A_137] :
      ( m1_subset_1(A_135,B_136)
      | ~ r2_hidden(A_135,A_137)
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(resolution,[status(thm)],[c_16,c_304])).

tff(c_506,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1('#skF_1'(A_138),B_139)
      | ~ r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_181,c_502])).

tff(c_391,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_409,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_391])).

tff(c_184,plain,(
    ! [A_74] : r2_hidden('#skF_1'(A_74),A_74) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_4])).

tff(c_40,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_48,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_189,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_40])).

tff(c_411,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_189])).

tff(c_541,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_506,c_411])).

tff(c_551,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_541])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_232,c_551])).

tff(c_556,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_111,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_49,c_111])).

tff(c_77,plain,(
    ! [A_57,B_58] :
      ( v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | ~ v1_xboole_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_57,B_58] :
      ( k2_zfmisc_1(A_57,B_58) = k1_xboole_0
      | ~ v1_xboole_0(B_58) ) ),
    inference(resolution,[status(thm)],[c_77,c_6])).

tff(c_565,plain,(
    ! [A_57] : k2_zfmisc_1(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_556,c_85])).

tff(c_1027,plain,(
    ! [A_202,B_203,C_204] :
      ( k1_relset_1(A_202,B_203,C_204) = k1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1053,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1027])).

tff(c_1055,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_42])).

tff(c_608,plain,(
    ! [C_141,A_142,B_143] :
      ( v1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_625,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_608])).

tff(c_632,plain,(
    ! [C_146,B_147,A_148] :
      ( v5_relat_1(C_146,B_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_651,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_632])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1074,plain,(
    ! [D_206,C_207,B_208,A_209] :
      ( m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(C_207,B_208)))
      | ~ r1_tarski(k2_relat_1(D_206),B_208)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(C_207,A_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1215,plain,(
    ! [B_223] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_223)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_223) ) ),
    inference(resolution,[status(thm)],[c_44,c_1074])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1326,plain,(
    ! [B_227] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_2',B_227))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_227) ) ),
    inference(resolution,[status(thm)],[c_1215,c_14])).

tff(c_1345,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2',k2_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_119,c_1326])).

tff(c_704,plain,(
    ! [C_158,B_159,A_160] :
      ( ~ v1_xboole_0(C_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(C_158))
      | ~ r2_hidden(A_160,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1096,plain,(
    ! [B_210,A_211,A_212] :
      ( ~ v1_xboole_0(B_210)
      | ~ r2_hidden(A_211,A_212)
      | ~ r1_tarski(A_212,B_210) ) ),
    inference(resolution,[status(thm)],[c_16,c_704])).

tff(c_1099,plain,(
    ! [B_210,A_1] :
      ( ~ v1_xboole_0(B_210)
      | ~ r1_tarski(A_1,B_210)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1096])).

tff(c_1365,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_4')))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1345,c_1099])).

tff(c_1372,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1365])).

tff(c_1395,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_1372])).

tff(c_847,plain,(
    ! [A_183,C_184,B_185] :
      ( m1_subset_1(A_183,C_184)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(C_184))
      | ~ r2_hidden(A_183,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1208,plain,(
    ! [A_220,B_221,A_222] :
      ( m1_subset_1(A_220,B_221)
      | ~ r2_hidden(A_220,A_222)
      | ~ r1_tarski(A_222,B_221) ) ),
    inference(resolution,[status(thm)],[c_16,c_847])).

tff(c_1586,plain,(
    ! [A_243,B_244] :
      ( m1_subset_1('#skF_1'(A_243),B_244)
      | ~ r1_tarski(A_243,B_244)
      | v1_xboole_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_4,c_1208])).

tff(c_955,plain,(
    ! [A_191,B_192,C_193] :
      ( k2_relset_1(A_191,B_192,C_193) = k2_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_981,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_955])).

tff(c_141,plain,(
    ! [D_69] :
      ( ~ r2_hidden(D_69,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_69,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_146,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_569,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_984,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_569])).

tff(c_1600,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1586,c_984])).

tff(c_1636,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1395,c_1600])).

tff(c_1647,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1636])).

tff(c_1651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_651,c_1647])).

tff(c_1652,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1365])).

tff(c_66,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_1677,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1652,c_66])).

tff(c_1685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1055,c_1677])).

tff(c_1686,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_1734,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1686,c_6])).

tff(c_2484,plain,(
    ! [A_334,B_335,C_336] :
      ( k2_relset_1(A_334,B_335,C_336) = k2_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2501,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2484])).

tff(c_2509,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_2501])).

tff(c_2702,plain,(
    ! [D_348,C_349,B_350,A_351] :
      ( m1_subset_1(D_348,k1_zfmisc_1(k2_zfmisc_1(C_349,B_350)))
      | ~ r1_tarski(k2_relat_1(D_348),B_350)
      | ~ m1_subset_1(D_348,k1_zfmisc_1(k2_zfmisc_1(C_349,A_351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2716,plain,(
    ! [B_350] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_350)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_350) ) ),
    inference(resolution,[status(thm)],[c_44,c_2702])).

tff(c_2741,plain,(
    ! [B_357] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_357)))
      | ~ r1_tarski(k1_xboole_0,B_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2509,c_2716])).

tff(c_2818,plain,(
    ! [B_358] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_2',B_358))
      | ~ r1_tarski(k1_xboole_0,B_358) ) ),
    inference(resolution,[status(thm)],[c_2741,c_14])).

tff(c_2838,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_2818])).

tff(c_2850,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2838])).

tff(c_1886,plain,(
    ! [C_271,B_272,A_273] :
      ( ~ v1_xboole_0(C_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(C_271))
      | ~ r2_hidden(A_273,B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1970,plain,(
    ! [B_288,A_289,A_290] :
      ( ~ v1_xboole_0(B_288)
      | ~ r2_hidden(A_289,A_290)
      | ~ r1_tarski(A_290,B_288) ) ),
    inference(resolution,[status(thm)],[c_16,c_1886])).

tff(c_1973,plain,(
    ! [B_288,A_1] :
      ( ~ v1_xboole_0(B_288)
      | ~ r1_tarski(A_1,B_288)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1970])).

tff(c_2853,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2850,c_1973])).

tff(c_2859,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_2853])).

tff(c_2866,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2859,c_66])).

tff(c_2874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2697,c_2866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.91/1.94  
% 4.91/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.91/1.94  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.91/1.94  
% 4.91/1.94  %Foreground sorts:
% 4.91/1.94  
% 4.91/1.94  
% 4.91/1.94  %Background operators:
% 4.91/1.94  
% 4.91/1.94  
% 4.91/1.94  %Foreground operators:
% 4.91/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.91/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.91/1.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.91/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.91/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.91/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.91/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.91/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.91/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.91/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.91/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.91/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.91/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.91/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.91/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.91/1.94  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.91/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.91/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.91/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.91/1.94  
% 4.91/1.97  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 4.91/1.97  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.91/1.97  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.91/1.97  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.91/1.97  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.91/1.97  tff(f_70, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.91/1.97  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.91/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.91/1.97  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.91/1.97  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.91/1.97  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.91/1.97  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.91/1.97  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.91/1.97  tff(f_39, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 4.91/1.97  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 4.91/1.97  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.91/1.97  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.91/1.97  tff(c_2668, plain, (![A_345, B_346, C_347]: (k1_relset_1(A_345, B_346, C_347)=k1_relat_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.91/1.97  tff(c_2695, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2668])).
% 4.91/1.97  tff(c_42, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.91/1.97  tff(c_2697, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2695, c_42])).
% 4.91/1.97  tff(c_190, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.91/1.97  tff(c_203, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_190])).
% 4.91/1.97  tff(c_219, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.91/1.97  tff(c_232, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_219])).
% 4.91/1.97  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.91/1.97  tff(c_26, plain, (![A_20]: (v1_xboole_0(k1_relat_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.91/1.97  tff(c_62, plain, (![A_54]: (v1_xboole_0(k1_relat_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.91/1.97  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.91/1.97  tff(c_67, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_62, c_6])).
% 4.91/1.97  tff(c_93, plain, (![A_61]: (k1_relat_1(k1_relat_1(A_61))=k1_xboole_0 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_26, c_67])).
% 4.91/1.97  tff(c_102, plain, (![A_61]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_61)) | ~v1_xboole_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_93, c_26])).
% 4.91/1.97  tff(c_169, plain, (![A_72]: (~v1_xboole_0(k1_relat_1(A_72)) | ~v1_xboole_0(A_72))), inference(splitLeft, [status(thm)], [c_102])).
% 4.91/1.97  tff(c_179, plain, (![A_20]: (~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_26, c_169])).
% 4.91/1.97  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.91/1.97  tff(c_181, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_179, c_4])).
% 4.91/1.97  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.91/1.97  tff(c_304, plain, (![A_104, C_105, B_106]: (m1_subset_1(A_104, C_105) | ~m1_subset_1(B_106, k1_zfmisc_1(C_105)) | ~r2_hidden(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.91/1.97  tff(c_502, plain, (![A_135, B_136, A_137]: (m1_subset_1(A_135, B_136) | ~r2_hidden(A_135, A_137) | ~r1_tarski(A_137, B_136))), inference(resolution, [status(thm)], [c_16, c_304])).
% 4.91/1.97  tff(c_506, plain, (![A_138, B_139]: (m1_subset_1('#skF_1'(A_138), B_139) | ~r1_tarski(A_138, B_139))), inference(resolution, [status(thm)], [c_181, c_502])).
% 4.91/1.97  tff(c_391, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.91/1.97  tff(c_409, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_391])).
% 4.91/1.97  tff(c_184, plain, (![A_74]: (r2_hidden('#skF_1'(A_74), A_74))), inference(negUnitSimplification, [status(thm)], [c_179, c_4])).
% 4.91/1.97  tff(c_40, plain, (![D_48]: (~r2_hidden(D_48, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_48, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.91/1.97  tff(c_189, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_184, c_40])).
% 4.91/1.97  tff(c_411, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_189])).
% 4.91/1.97  tff(c_541, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_506, c_411])).
% 4.91/1.97  tff(c_551, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_541])).
% 4.91/1.97  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_232, c_551])).
% 4.91/1.97  tff(c_556, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_102])).
% 4.91/1.97  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.91/1.97  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.91/1.97  tff(c_49, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.91/1.98  tff(c_111, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.91/1.98  tff(c_119, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_49, c_111])).
% 4.91/1.98  tff(c_77, plain, (![A_57, B_58]: (v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | ~v1_xboole_0(B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.91/1.98  tff(c_85, plain, (![A_57, B_58]: (k2_zfmisc_1(A_57, B_58)=k1_xboole_0 | ~v1_xboole_0(B_58))), inference(resolution, [status(thm)], [c_77, c_6])).
% 4.91/1.98  tff(c_565, plain, (![A_57]: (k2_zfmisc_1(A_57, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_556, c_85])).
% 4.91/1.98  tff(c_1027, plain, (![A_202, B_203, C_204]: (k1_relset_1(A_202, B_203, C_204)=k1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.91/1.98  tff(c_1053, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1027])).
% 4.91/1.98  tff(c_1055, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_42])).
% 4.91/1.98  tff(c_608, plain, (![C_141, A_142, B_143]: (v1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.91/1.98  tff(c_625, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_608])).
% 4.91/1.98  tff(c_632, plain, (![C_146, B_147, A_148]: (v5_relat_1(C_146, B_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.91/1.98  tff(c_651, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_632])).
% 4.91/1.98  tff(c_8, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.91/1.98  tff(c_1074, plain, (![D_206, C_207, B_208, A_209]: (m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(C_207, B_208))) | ~r1_tarski(k2_relat_1(D_206), B_208) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(C_207, A_209))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.91/1.98  tff(c_1215, plain, (![B_223]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_223))) | ~r1_tarski(k2_relat_1('#skF_4'), B_223))), inference(resolution, [status(thm)], [c_44, c_1074])).
% 4.91/1.98  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.91/1.98  tff(c_1326, plain, (![B_227]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', B_227)) | ~r1_tarski(k2_relat_1('#skF_4'), B_227))), inference(resolution, [status(thm)], [c_1215, c_14])).
% 4.91/1.98  tff(c_1345, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_119, c_1326])).
% 4.91/1.98  tff(c_704, plain, (![C_158, B_159, A_160]: (~v1_xboole_0(C_158) | ~m1_subset_1(B_159, k1_zfmisc_1(C_158)) | ~r2_hidden(A_160, B_159))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.91/1.98  tff(c_1096, plain, (![B_210, A_211, A_212]: (~v1_xboole_0(B_210) | ~r2_hidden(A_211, A_212) | ~r1_tarski(A_212, B_210))), inference(resolution, [status(thm)], [c_16, c_704])).
% 4.91/1.98  tff(c_1099, plain, (![B_210, A_1]: (~v1_xboole_0(B_210) | ~r1_tarski(A_1, B_210) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1096])).
% 4.91/1.98  tff(c_1365, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_4'))) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1345, c_1099])).
% 4.91/1.98  tff(c_1372, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_1365])).
% 4.91/1.98  tff(c_1395, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1372])).
% 4.91/1.98  tff(c_847, plain, (![A_183, C_184, B_185]: (m1_subset_1(A_183, C_184) | ~m1_subset_1(B_185, k1_zfmisc_1(C_184)) | ~r2_hidden(A_183, B_185))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.91/1.98  tff(c_1208, plain, (![A_220, B_221, A_222]: (m1_subset_1(A_220, B_221) | ~r2_hidden(A_220, A_222) | ~r1_tarski(A_222, B_221))), inference(resolution, [status(thm)], [c_16, c_847])).
% 4.91/1.98  tff(c_1586, plain, (![A_243, B_244]: (m1_subset_1('#skF_1'(A_243), B_244) | ~r1_tarski(A_243, B_244) | v1_xboole_0(A_243))), inference(resolution, [status(thm)], [c_4, c_1208])).
% 4.91/1.98  tff(c_955, plain, (![A_191, B_192, C_193]: (k2_relset_1(A_191, B_192, C_193)=k2_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.91/1.98  tff(c_981, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_955])).
% 4.91/1.98  tff(c_141, plain, (![D_69]: (~r2_hidden(D_69, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_69, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.91/1.98  tff(c_146, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_141])).
% 4.91/1.98  tff(c_569, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 4.91/1.98  tff(c_984, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_569])).
% 4.91/1.98  tff(c_1600, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1586, c_984])).
% 4.91/1.98  tff(c_1636, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1395, c_1600])).
% 4.91/1.98  tff(c_1647, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1636])).
% 4.91/1.98  tff(c_1651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_625, c_651, c_1647])).
% 4.91/1.98  tff(c_1652, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1365])).
% 4.91/1.98  tff(c_66, plain, (![A_54]: (k1_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_62, c_6])).
% 4.91/1.98  tff(c_1677, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1652, c_66])).
% 4.91/1.98  tff(c_1685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1055, c_1677])).
% 4.91/1.98  tff(c_1686, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_146])).
% 4.91/1.98  tff(c_1734, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1686, c_6])).
% 4.91/1.98  tff(c_2484, plain, (![A_334, B_335, C_336]: (k2_relset_1(A_334, B_335, C_336)=k2_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.91/1.98  tff(c_2501, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2484])).
% 4.91/1.98  tff(c_2509, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_2501])).
% 4.91/1.98  tff(c_2702, plain, (![D_348, C_349, B_350, A_351]: (m1_subset_1(D_348, k1_zfmisc_1(k2_zfmisc_1(C_349, B_350))) | ~r1_tarski(k2_relat_1(D_348), B_350) | ~m1_subset_1(D_348, k1_zfmisc_1(k2_zfmisc_1(C_349, A_351))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.91/1.98  tff(c_2716, plain, (![B_350]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_350))) | ~r1_tarski(k2_relat_1('#skF_4'), B_350))), inference(resolution, [status(thm)], [c_44, c_2702])).
% 4.91/1.98  tff(c_2741, plain, (![B_357]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_357))) | ~r1_tarski(k1_xboole_0, B_357))), inference(demodulation, [status(thm), theory('equality')], [c_2509, c_2716])).
% 4.91/1.98  tff(c_2818, plain, (![B_358]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', B_358)) | ~r1_tarski(k1_xboole_0, B_358))), inference(resolution, [status(thm)], [c_2741, c_14])).
% 4.91/1.98  tff(c_2838, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_565, c_2818])).
% 4.91/1.98  tff(c_2850, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2838])).
% 4.91/1.98  tff(c_1886, plain, (![C_271, B_272, A_273]: (~v1_xboole_0(C_271) | ~m1_subset_1(B_272, k1_zfmisc_1(C_271)) | ~r2_hidden(A_273, B_272))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.91/1.98  tff(c_1970, plain, (![B_288, A_289, A_290]: (~v1_xboole_0(B_288) | ~r2_hidden(A_289, A_290) | ~r1_tarski(A_290, B_288))), inference(resolution, [status(thm)], [c_16, c_1886])).
% 4.91/1.98  tff(c_1973, plain, (![B_288, A_1]: (~v1_xboole_0(B_288) | ~r1_tarski(A_1, B_288) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1970])).
% 4.91/1.98  tff(c_2853, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2850, c_1973])).
% 4.91/1.98  tff(c_2859, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_2853])).
% 4.91/1.98  tff(c_2866, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2859, c_66])).
% 4.91/1.98  tff(c_2874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2697, c_2866])).
% 4.91/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.91/1.98  
% 4.91/1.98  Inference rules
% 4.91/1.98  ----------------------
% 4.91/1.98  #Ref     : 0
% 4.91/1.98  #Sup     : 626
% 4.91/1.98  #Fact    : 0
% 4.91/1.98  #Define  : 0
% 4.91/1.98  #Split   : 8
% 4.91/1.98  #Chain   : 0
% 4.91/1.98  #Close   : 0
% 4.91/1.98  
% 4.91/1.98  Ordering : KBO
% 4.91/1.98  
% 4.91/1.98  Simplification rules
% 4.91/1.98  ----------------------
% 4.91/1.98  #Subsume      : 80
% 4.91/1.98  #Demod        : 277
% 4.91/1.98  #Tautology    : 218
% 4.91/1.98  #SimpNegUnit  : 18
% 4.91/1.98  #BackRed      : 19
% 4.91/1.98  
% 4.91/1.98  #Partial instantiations: 0
% 4.91/1.98  #Strategies tried      : 1
% 4.91/1.98  
% 4.91/1.98  Timing (in seconds)
% 4.91/1.98  ----------------------
% 5.15/1.98  Preprocessing        : 0.34
% 5.15/1.98  Parsing              : 0.18
% 5.15/1.98  CNF conversion       : 0.02
% 5.15/1.98  Main loop            : 0.82
% 5.15/1.98  Inferencing          : 0.30
% 5.15/1.98  Reduction            : 0.25
% 5.15/1.98  Demodulation         : 0.17
% 5.15/1.98  BG Simplification    : 0.03
% 5.15/1.98  Subsumption          : 0.16
% 5.15/1.98  Abstraction          : 0.04
% 5.15/1.98  MUC search           : 0.00
% 5.15/1.98  Cooper               : 0.00
% 5.15/1.98  Total                : 1.23
% 5.15/1.98  Index Insertion      : 0.00
% 5.15/1.98  Index Deletion       : 0.00
% 5.15/1.98  Index Matching       : 0.00
% 5.15/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
