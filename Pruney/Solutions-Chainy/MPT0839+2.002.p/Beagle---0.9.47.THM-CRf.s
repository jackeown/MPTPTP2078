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
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :  251 (1844 expanded)
%              Number of leaves         :   39 ( 608 expanded)
%              Depth                    :   19
%              Number of atoms          :  408 (3694 expanded)
%              Number of equality atoms :   72 ( 613 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_8,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_93,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_51,c_93])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_152,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_165,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_152])).

tff(c_108,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_121,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_108])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_933,plain,(
    ! [C_174,A_175,B_176] :
      ( v1_xboole_0(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_947,plain,(
    ! [A_175,B_176] :
      ( v1_xboole_0(k2_zfmisc_1(A_175,B_176))
      | ~ v1_xboole_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_51,c_933])).

tff(c_948,plain,(
    ! [A_177,B_178] :
      ( v1_xboole_0(k2_zfmisc_1(A_177,B_178))
      | ~ v1_xboole_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_51,c_933])).

tff(c_72,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_2'(A_56),A_56)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(A_56)
      | k1_xboole_0 = A_56 ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_957,plain,(
    ! [A_179,B_180] :
      ( k2_zfmisc_1(A_179,B_180) = k1_xboole_0
      | ~ v1_xboole_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_948,c_81])).

tff(c_974,plain,(
    ! [A_183,B_184,B_185] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_183,B_184),B_185) = k1_xboole_0
      | ~ v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_947,c_957])).

tff(c_166,plain,(
    ! [A_76,B_77] : v4_relat_1(k2_zfmisc_1(A_76,B_77),A_76) ),
    inference(resolution,[status(thm)],[c_51,c_152])).

tff(c_1446,plain,(
    ! [A_232,B_233] :
      ( v4_relat_1(k1_xboole_0,k2_zfmisc_1(A_232,B_233))
      | ~ v1_xboole_0(A_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_166])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_194,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k1_relat_1(B_88),A_89)
      | ~ v4_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_209,plain,(
    ! [A_89] :
      ( r1_tarski(k1_xboole_0,A_89)
      | ~ v4_relat_1(k1_xboole_0,A_89)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_194])).

tff(c_213,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_275,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_xboole_0(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_289,plain,(
    ! [A_104,B_105] :
      ( v1_xboole_0(k2_zfmisc_1(A_104,B_105))
      | ~ v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_51,c_275])).

tff(c_300,plain,(
    ! [A_109,B_110] :
      ( v1_xboole_0(k2_zfmisc_1(A_109,B_110))
      | ~ v1_xboole_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_51,c_275])).

tff(c_318,plain,(
    ! [A_113,B_114] :
      ( k2_zfmisc_1(A_113,B_114) = k1_xboole_0
      | ~ v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_300,c_81])).

tff(c_415,plain,(
    ! [A_119,B_120,B_121] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_119,B_120),B_121) = k1_xboole_0
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_289,c_318])).

tff(c_122,plain,(
    ! [A_65,B_66] : v1_relat_1(k2_zfmisc_1(A_65,B_66)) ),
    inference(resolution,[status(thm)],[c_51,c_108])).

tff(c_449,plain,(
    ! [A_119] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_122])).

tff(c_459,plain,(
    ! [A_119] : ~ v1_xboole_0(A_119) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_449])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_466,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_4])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_290,plain,(
    ! [A_106,C_107,B_108] :
      ( m1_subset_1(A_106,C_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(C_107))
      | ~ r2_hidden(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_795,plain,(
    ! [A_154,B_155,A_156] :
      ( m1_subset_1(A_154,B_155)
      | ~ r2_hidden(A_154,A_156)
      | ~ r1_tarski(A_156,B_155) ) ),
    inference(resolution,[status(thm)],[c_14,c_290])).

tff(c_811,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1('#skF_1'(A_159),B_160)
      | ~ r1_tarski(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_466,c_795])).

tff(c_520,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_543,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_520])).

tff(c_83,plain,(
    ! [A_58] :
      ( v1_xboole_0(A_58)
      | r2_hidden('#skF_1'(A_58),A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_91,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_83,c_42])).

tff(c_123,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_547,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_123])).

tff(c_847,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_811,c_547])).

tff(c_856,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_847])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_165,c_856])).

tff(c_861,plain,(
    ! [A_89] :
      ( r1_tarski(k1_xboole_0,A_89)
      | ~ v4_relat_1(k1_xboole_0,A_89) ) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_1823,plain,(
    ! [A_270,B_271] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_270,B_271))
      | ~ v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_1446,c_861])).

tff(c_164,plain,(
    ! [A_9,A_76,B_77] :
      ( v4_relat_1(A_9,A_76)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_14,c_152])).

tff(c_1851,plain,(
    ! [A_272] :
      ( v4_relat_1(k1_xboole_0,A_272)
      | ~ v1_xboole_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_1823,c_164])).

tff(c_1856,plain,(
    ! [A_273] :
      ( r1_tarski(k1_xboole_0,A_273)
      | ~ v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_1851,c_861])).

tff(c_863,plain,(
    ! [C_161,B_162,A_163] :
      ( ~ v1_xboole_0(C_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(C_161))
      | ~ r2_hidden(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_875,plain,(
    ! [B_165,A_166,A_167] :
      ( ~ v1_xboole_0(B_165)
      | ~ r2_hidden(A_166,A_167)
      | ~ r1_tarski(A_167,B_165) ) ),
    inference(resolution,[status(thm)],[c_14,c_863])).

tff(c_880,plain,(
    ! [B_165,A_1] :
      ( ~ v1_xboole_0(B_165)
      | ~ r1_tarski(A_1,B_165)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_875])).

tff(c_1883,plain,(
    ! [A_273] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_1856,c_880])).

tff(c_1889,plain,(
    ! [A_273] : ~ v1_xboole_0(A_273) ),
    inference(splitLeft,[status(thm)],[c_1883])).

tff(c_1894,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_1889,c_4])).

tff(c_1359,plain,(
    ! [A_225,C_226,B_227] :
      ( m1_subset_1(A_225,C_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(C_226))
      | ~ r2_hidden(A_225,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2266,plain,(
    ! [A_303,B_304,A_305] :
      ( m1_subset_1(A_303,B_304)
      | ~ r2_hidden(A_303,A_305)
      | ~ r1_tarski(A_305,B_304) ) ),
    inference(resolution,[status(thm)],[c_14,c_1359])).

tff(c_2273,plain,(
    ! [A_306,B_307] :
      ( m1_subset_1('#skF_1'(A_306),B_307)
      | ~ r1_tarski(A_306,B_307) ) ),
    inference(resolution,[status(thm)],[c_1894,c_2266])).

tff(c_1953,plain,(
    ! [A_278,B_279,C_280] :
      ( k1_relset_1(A_278,B_279,C_280) = k1_relat_1(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1976,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1953])).

tff(c_1979,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_123])).

tff(c_2314,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2273,c_1979])).

tff(c_2323,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_2314])).

tff(c_2327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_165,c_2323])).

tff(c_2328,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1883])).

tff(c_956,plain,(
    ! [A_177,B_178] :
      ( k2_zfmisc_1(A_177,B_178) = k1_xboole_0
      | ~ v1_xboole_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_948,c_81])).

tff(c_2334,plain,(
    ! [B_178] : k2_zfmisc_1(k1_xboole_0,B_178) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2328,c_956])).

tff(c_2888,plain,(
    ! [A_346,B_347,A_348] :
      ( m1_subset_1(A_346,B_347)
      | ~ r2_hidden(A_346,A_348)
      | ~ r1_tarski(A_348,B_347) ) ),
    inference(resolution,[status(thm)],[c_14,c_1359])).

tff(c_3514,plain,(
    ! [A_380,B_381] :
      ( m1_subset_1('#skF_2'(A_380),B_381)
      | ~ r1_tarski(A_380,B_381)
      | k1_xboole_0 = A_380 ) ),
    inference(resolution,[status(thm)],[c_6,c_2888])).

tff(c_2441,plain,(
    ! [A_315,B_316,C_317] :
      ( k1_relset_1(A_315,B_316,C_317) = k1_relat_1(C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2470,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_2441])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_42])).

tff(c_169,plain,(
    ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_2472,plain,(
    ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2470,c_169])).

tff(c_3576,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3514,c_2472])).

tff(c_3641,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3576])).

tff(c_3644,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_3641])).

tff(c_3648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_165,c_3644])).

tff(c_3649,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3576])).

tff(c_2590,plain,(
    ! [D_325,B_326,C_327,A_328] :
      ( m1_subset_1(D_325,k1_zfmisc_1(k2_zfmisc_1(B_326,C_327)))
      | ~ r1_tarski(k1_relat_1(D_325),B_326)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(k2_zfmisc_1(A_328,C_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2640,plain,(
    ! [B_331] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_331,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_331) ) ),
    inference(resolution,[status(thm)],[c_46,c_2590])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3129,plain,(
    ! [B_360] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_360,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_360) ) ),
    inference(resolution,[status(thm)],[c_2640,c_12])).

tff(c_3148,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_101,c_3129])).

tff(c_881,plain,(
    ! [B_165,A_5] :
      ( ~ v1_xboole_0(B_165)
      | ~ r1_tarski(A_5,B_165)
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_6,c_875])).

tff(c_3168,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3148,c_881])).

tff(c_3176,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3168])).

tff(c_3655,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3649,c_3176])).

tff(c_3671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2328,c_2334,c_3655])).

tff(c_3672,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3168])).

tff(c_2365,plain,(
    ! [B_311] : k2_zfmisc_1(k1_xboole_0,B_311) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2328,c_956])).

tff(c_2388,plain,(
    ! [A_9] :
      ( v4_relat_1(A_9,k1_xboole_0)
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2365,c_164])).

tff(c_34,plain,(
    ! [C_28,A_25,B_26] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2680,plain,(
    ! [B_331] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_331)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_331) ) ),
    inference(resolution,[status(thm)],[c_2640,c_34])).

tff(c_2899,plain,(
    ! [B_349] :
      ( ~ v1_xboole_0(B_349)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_349) ) ),
    inference(splitLeft,[status(thm)],[c_2680])).

tff(c_2907,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | ~ v4_relat_1('#skF_5',A_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_2899])).

tff(c_2919,plain,(
    ! [A_350] :
      ( ~ v1_xboole_0(A_350)
      | ~ v4_relat_1('#skF_5',A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_2907])).

tff(c_2930,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2388,c_2919])).

tff(c_2944,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2328,c_2930])).

tff(c_3699,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_2944])).

tff(c_3738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3699])).

tff(c_3739,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2680])).

tff(c_3746,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3739,c_81])).

tff(c_2337,plain,(
    ! [A_308,B_309,C_310] :
      ( k2_relset_1(A_308,B_309,C_310) = k2_relat_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2363,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_2337])).

tff(c_44,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2427,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_44])).

tff(c_3761,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_2427])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3780,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_3746,c_24])).

tff(c_3797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3761,c_3780])).

tff(c_3798,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_4961,plain,(
    ! [A_516,B_517,C_518] :
      ( k1_relset_1(A_516,B_517,C_518) = k1_relat_1(C_518)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4979,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_4961])).

tff(c_4988,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3798,c_4979])).

tff(c_4999,plain,(
    ! [A_17] :
      ( r1_tarski(k1_xboole_0,A_17)
      | ~ v4_relat_1('#skF_5',A_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4988,c_22])).

tff(c_5010,plain,(
    ! [A_520] :
      ( r1_tarski(k1_xboole_0,A_520)
      | ~ v4_relat_1('#skF_5',A_520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4999])).

tff(c_5030,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_5010])).

tff(c_4365,plain,(
    ! [C_453,A_454,B_455] :
      ( v1_xboole_0(C_453)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ v1_xboole_0(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4379,plain,(
    ! [A_454,B_455] :
      ( v1_xboole_0(k2_zfmisc_1(A_454,B_455))
      | ~ v1_xboole_0(A_454) ) ),
    inference(resolution,[status(thm)],[c_51,c_4365])).

tff(c_4380,plain,(
    ! [A_456,B_457] :
      ( v1_xboole_0(k2_zfmisc_1(A_456,B_457))
      | ~ v1_xboole_0(A_456) ) ),
    inference(resolution,[status(thm)],[c_51,c_4365])).

tff(c_4389,plain,(
    ! [A_458,B_459] :
      ( k2_zfmisc_1(A_458,B_459) = k1_xboole_0
      | ~ v1_xboole_0(A_458) ) ),
    inference(resolution,[status(thm)],[c_4380,c_81])).

tff(c_4538,plain,(
    ! [A_476,B_477,B_478] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_476,B_477),B_478) = k1_xboole_0
      | ~ v1_xboole_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_4379,c_4389])).

tff(c_4952,plain,(
    ! [A_514,B_515] :
      ( v4_relat_1(k1_xboole_0,k2_zfmisc_1(A_514,B_515))
      | ~ v1_xboole_0(A_514) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4538,c_166])).

tff(c_3843,plain,(
    ! [B_395,A_396] :
      ( r1_tarski(k1_relat_1(B_395),A_396)
      | ~ v4_relat_1(B_395,A_396)
      | ~ v1_relat_1(B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3858,plain,(
    ! [A_396] :
      ( r1_tarski(k1_xboole_0,A_396)
      | ~ v4_relat_1(k1_xboole_0,A_396)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3843])).

tff(c_3862,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3858])).

tff(c_3924,plain,(
    ! [A_410,C_411,B_412] :
      ( m1_subset_1(A_410,C_411)
      | ~ m1_subset_1(B_412,k1_zfmisc_1(C_411))
      | ~ r2_hidden(A_410,B_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4050,plain,(
    ! [A_420,B_421,A_422] :
      ( m1_subset_1(A_420,B_421)
      | ~ r2_hidden(A_420,A_422)
      | ~ r1_tarski(A_422,B_421) ) ),
    inference(resolution,[status(thm)],[c_14,c_3924])).

tff(c_4057,plain,(
    ! [A_423,B_424] :
      ( m1_subset_1('#skF_1'(A_423),B_424)
      | ~ r1_tarski(A_423,B_424)
      | v1_xboole_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_4,c_4050])).

tff(c_3800,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3798,c_123])).

tff(c_4085,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4057,c_3800])).

tff(c_4090,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4085])).

tff(c_4134,plain,(
    ! [A_432,B_433,C_434] :
      ( k1_relset_1(A_432,B_433,C_434) = k1_relat_1(C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4153,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_4134])).

tff(c_4163,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3798,c_4153])).

tff(c_4174,plain,(
    ! [A_17] :
      ( r1_tarski(k1_xboole_0,A_17)
      | ~ v4_relat_1('#skF_5',A_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4163,c_22])).

tff(c_4185,plain,(
    ! [A_436] :
      ( r1_tarski(k1_xboole_0,A_436)
      | ~ v4_relat_1('#skF_5',A_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4174])).

tff(c_4198,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_4185])).

tff(c_4208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4090,c_4198])).

tff(c_4209,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4085])).

tff(c_4216,plain,(
    ! [C_437,A_438,B_439] :
      ( v1_xboole_0(C_437)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ v1_xboole_0(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4255,plain,(
    ! [A_440,B_441] :
      ( v1_xboole_0(k2_zfmisc_1(A_440,B_441))
      | ~ v1_xboole_0(A_440) ) ),
    inference(resolution,[status(thm)],[c_51,c_4216])).

tff(c_4264,plain,(
    ! [A_442,B_443] :
      ( k2_zfmisc_1(A_442,B_443) = k1_xboole_0
      | ~ v1_xboole_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_4255,c_81])).

tff(c_4271,plain,(
    ! [B_444] : k2_zfmisc_1(k1_xboole_0,B_444) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4209,c_4264])).

tff(c_4301,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4271,c_122])).

tff(c_4312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3862,c_4301])).

tff(c_4313,plain,(
    ! [A_396] :
      ( r1_tarski(k1_xboole_0,A_396)
      | ~ v4_relat_1(k1_xboole_0,A_396) ) ),
    inference(splitRight,[status(thm)],[c_3858])).

tff(c_5260,plain,(
    ! [A_544,B_545] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_544,B_545))
      | ~ v1_xboole_0(A_544) ) ),
    inference(resolution,[status(thm)],[c_4952,c_4313])).

tff(c_5288,plain,(
    ! [A_546] :
      ( v4_relat_1(k1_xboole_0,A_546)
      | ~ v1_xboole_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_5260,c_164])).

tff(c_5293,plain,(
    ! [A_547] :
      ( r1_tarski(k1_xboole_0,A_547)
      | ~ v1_xboole_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_5288,c_4313])).

tff(c_4349,plain,(
    ! [C_450,B_451,A_452] :
      ( ~ v1_xboole_0(C_450)
      | ~ m1_subset_1(B_451,k1_zfmisc_1(C_450))
      | ~ r2_hidden(A_452,B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4393,plain,(
    ! [B_460,A_461,A_462] :
      ( ~ v1_xboole_0(B_460)
      | ~ r2_hidden(A_461,A_462)
      | ~ r1_tarski(A_462,B_460) ) ),
    inference(resolution,[status(thm)],[c_14,c_4349])).

tff(c_4398,plain,(
    ! [B_460,A_1] :
      ( ~ v1_xboole_0(B_460)
      | ~ r1_tarski(A_1,B_460)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_4393])).

tff(c_5320,plain,(
    ! [A_547] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_5293,c_4398])).

tff(c_5326,plain,(
    ! [A_547] : ~ v1_xboole_0(A_547) ),
    inference(splitLeft,[status(thm)],[c_5320])).

tff(c_5340,plain,(
    ! [A_552] : r2_hidden('#skF_1'(A_552),A_552) ),
    inference(negUnitSimplification,[status(thm)],[c_5326,c_4])).

tff(c_4426,plain,(
    ! [A_467,C_468,B_469] :
      ( m1_subset_1(A_467,C_468)
      | ~ m1_subset_1(B_469,k1_zfmisc_1(C_468))
      | ~ r2_hidden(A_467,B_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4433,plain,(
    ! [A_467,B_10,A_9] :
      ( m1_subset_1(A_467,B_10)
      | ~ r2_hidden(A_467,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_4426])).

tff(c_5452,plain,(
    ! [A_558,B_559] :
      ( m1_subset_1('#skF_1'(A_558),B_559)
      | ~ r1_tarski(A_558,B_559) ) ),
    inference(resolution,[status(thm)],[c_5340,c_4433])).

tff(c_5469,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_5452,c_3800])).

tff(c_5493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5030,c_5469])).

tff(c_5494,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5320])).

tff(c_4388,plain,(
    ! [A_456,B_457] :
      ( k2_zfmisc_1(A_456,B_457) = k1_xboole_0
      | ~ v1_xboole_0(A_456) ) ),
    inference(resolution,[status(thm)],[c_4380,c_81])).

tff(c_5500,plain,(
    ! [B_457] : k2_zfmisc_1(k1_xboole_0,B_457) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5494,c_4388])).

tff(c_5220,plain,(
    ! [D_539,B_540,C_541,A_542] :
      ( m1_subset_1(D_539,k1_zfmisc_1(k2_zfmisc_1(B_540,C_541)))
      | ~ r1_tarski(k1_relat_1(D_539),B_540)
      | ~ m1_subset_1(D_539,k1_zfmisc_1(k2_zfmisc_1(A_542,C_541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5233,plain,(
    ! [B_540] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_540,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_540) ) ),
    inference(resolution,[status(thm)],[c_46,c_5220])).

tff(c_5570,plain,(
    ! [B_561] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_561,'#skF_3')))
      | ~ r1_tarski(k1_xboole_0,B_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4988,c_5233])).

tff(c_5601,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5500,c_5570])).

tff(c_5621,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5601])).

tff(c_18,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5625,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_14,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5621,c_18])).

tff(c_5634,plain,(
    ! [A_562] : ~ r2_hidden(A_562,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5494,c_5625])).

tff(c_5644,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_5634])).

tff(c_5683,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5644,c_5644,c_24])).

tff(c_5039,plain,(
    ! [A_521,B_522,C_523] :
      ( k2_relset_1(A_521,B_522,C_523) = k2_relat_1(C_523)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5065,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_5039])).

tff(c_5067,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5065,c_44])).

tff(c_5660,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5644,c_5067])).

tff(c_5723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5683,c_5660])).

tff(c_5724,plain,(
    v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_5730,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5724,c_81])).

tff(c_5731,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5730,c_5724])).

tff(c_6244,plain,(
    ! [C_646,A_647,B_648] :
      ( v1_xboole_0(C_646)
      | ~ m1_subset_1(C_646,k1_zfmisc_1(k2_zfmisc_1(A_647,B_648)))
      | ~ v1_xboole_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6268,plain,(
    ! [A_651,B_652] :
      ( v1_xboole_0(k2_zfmisc_1(A_651,B_652))
      | ~ v1_xboole_0(A_651) ) ),
    inference(resolution,[status(thm)],[c_51,c_6244])).

tff(c_6346,plain,(
    ! [A_656,B_657] :
      ( k2_zfmisc_1(A_656,B_657) = k1_xboole_0
      | ~ v1_xboole_0(A_656) ) ),
    inference(resolution,[status(thm)],[c_6268,c_81])).

tff(c_6352,plain,(
    ! [B_657] : k2_zfmisc_1(k1_xboole_0,B_657) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5731,c_6346])).

tff(c_6547,plain,(
    ! [A_673,B_674,C_675] :
      ( k1_relset_1(A_673,B_674,C_675) = k1_relat_1(C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(A_673,B_674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6565,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_6547])).

tff(c_6574,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5730,c_6565])).

tff(c_6929,plain,(
    ! [D_688,B_689,C_690,A_691] :
      ( m1_subset_1(D_688,k1_zfmisc_1(k2_zfmisc_1(B_689,C_690)))
      | ~ r1_tarski(k1_relat_1(D_688),B_689)
      | ~ m1_subset_1(D_688,k1_zfmisc_1(k2_zfmisc_1(A_691,C_690))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6942,plain,(
    ! [B_689] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_689,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_689) ) ),
    inference(resolution,[status(thm)],[c_46,c_6929])).

tff(c_6972,plain,(
    ! [B_693] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_693,'#skF_3')))
      | ~ r1_tarski(k1_xboole_0,B_693) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6574,c_6942])).

tff(c_7003,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6352,c_6972])).

tff(c_7019,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_7003])).

tff(c_6353,plain,(
    ! [B_658] : k2_zfmisc_1(k1_xboole_0,B_658) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5731,c_6346])).

tff(c_6361,plain,(
    ! [C_28] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6353,c_34])).

tff(c_6392,plain,(
    ! [C_28] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5731,c_6361])).

tff(c_7041,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_7019,c_6392])).

tff(c_7055,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7041,c_81])).

tff(c_6409,plain,(
    ! [A_661,B_662,C_663] :
      ( k2_relset_1(A_661,B_662,C_663) = k2_relat_1(C_663)
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(A_661,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6435,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_6409])).

tff(c_6437,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6435,c_44])).

tff(c_7075,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7055,c_6437])).

tff(c_7092,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7055,c_7055,c_24])).

tff(c_7132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7075,c_7092])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.50  
% 6.21/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.50  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 6.21/2.50  
% 6.21/2.50  %Foreground sorts:
% 6.21/2.50  
% 6.21/2.50  
% 6.21/2.50  %Background operators:
% 6.21/2.50  
% 6.21/2.50  
% 6.21/2.50  %Foreground operators:
% 6.21/2.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.21/2.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.21/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.21/2.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.21/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.21/2.50  tff('#skF_5', type, '#skF_5': $i).
% 6.21/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.21/2.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.21/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.21/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.50  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.21/2.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.21/2.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.21/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.21/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.50  
% 6.21/2.53  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.21/2.53  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.21/2.53  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.21/2.53  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.21/2.53  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 6.21/2.53  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.21/2.53  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.21/2.53  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.21/2.53  tff(f_86, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.21/2.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.21/2.53  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.21/2.53  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.21/2.53  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.21/2.53  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.21/2.53  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 6.21/2.53  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.21/2.53  tff(c_8, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.21/2.53  tff(c_10, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.21/2.53  tff(c_51, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 6.21/2.53  tff(c_93, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.21/2.53  tff(c_101, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(resolution, [status(thm)], [c_51, c_93])).
% 6.21/2.53  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.21/2.53  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.21/2.53  tff(c_152, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.21/2.53  tff(c_165, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_152])).
% 6.21/2.53  tff(c_108, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.21/2.53  tff(c_121, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_108])).
% 6.21/2.53  tff(c_22, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.21/2.53  tff(c_933, plain, (![C_174, A_175, B_176]: (v1_xboole_0(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.21/2.53  tff(c_947, plain, (![A_175, B_176]: (v1_xboole_0(k2_zfmisc_1(A_175, B_176)) | ~v1_xboole_0(A_175))), inference(resolution, [status(thm)], [c_51, c_933])).
% 6.21/2.53  tff(c_948, plain, (![A_177, B_178]: (v1_xboole_0(k2_zfmisc_1(A_177, B_178)) | ~v1_xboole_0(A_177))), inference(resolution, [status(thm)], [c_51, c_933])).
% 6.21/2.53  tff(c_72, plain, (![A_56]: (r2_hidden('#skF_2'(A_56), A_56) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.21/2.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.53  tff(c_81, plain, (![A_56]: (~v1_xboole_0(A_56) | k1_xboole_0=A_56)), inference(resolution, [status(thm)], [c_72, c_2])).
% 6.21/2.53  tff(c_957, plain, (![A_179, B_180]: (k2_zfmisc_1(A_179, B_180)=k1_xboole_0 | ~v1_xboole_0(A_179))), inference(resolution, [status(thm)], [c_948, c_81])).
% 6.21/2.53  tff(c_974, plain, (![A_183, B_184, B_185]: (k2_zfmisc_1(k2_zfmisc_1(A_183, B_184), B_185)=k1_xboole_0 | ~v1_xboole_0(A_183))), inference(resolution, [status(thm)], [c_947, c_957])).
% 6.21/2.53  tff(c_166, plain, (![A_76, B_77]: (v4_relat_1(k2_zfmisc_1(A_76, B_77), A_76))), inference(resolution, [status(thm)], [c_51, c_152])).
% 6.21/2.53  tff(c_1446, plain, (![A_232, B_233]: (v4_relat_1(k1_xboole_0, k2_zfmisc_1(A_232, B_233)) | ~v1_xboole_0(A_232))), inference(superposition, [status(thm), theory('equality')], [c_974, c_166])).
% 6.21/2.53  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.21/2.53  tff(c_194, plain, (![B_88, A_89]: (r1_tarski(k1_relat_1(B_88), A_89) | ~v4_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.21/2.53  tff(c_209, plain, (![A_89]: (r1_tarski(k1_xboole_0, A_89) | ~v4_relat_1(k1_xboole_0, A_89) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_194])).
% 6.21/2.53  tff(c_213, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_209])).
% 6.21/2.53  tff(c_275, plain, (![C_103, A_104, B_105]: (v1_xboole_0(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.21/2.53  tff(c_289, plain, (![A_104, B_105]: (v1_xboole_0(k2_zfmisc_1(A_104, B_105)) | ~v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_51, c_275])).
% 6.21/2.53  tff(c_300, plain, (![A_109, B_110]: (v1_xboole_0(k2_zfmisc_1(A_109, B_110)) | ~v1_xboole_0(A_109))), inference(resolution, [status(thm)], [c_51, c_275])).
% 6.21/2.53  tff(c_318, plain, (![A_113, B_114]: (k2_zfmisc_1(A_113, B_114)=k1_xboole_0 | ~v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_300, c_81])).
% 6.21/2.53  tff(c_415, plain, (![A_119, B_120, B_121]: (k2_zfmisc_1(k2_zfmisc_1(A_119, B_120), B_121)=k1_xboole_0 | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_289, c_318])).
% 6.21/2.53  tff(c_122, plain, (![A_65, B_66]: (v1_relat_1(k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_51, c_108])).
% 6.21/2.53  tff(c_449, plain, (![A_119]: (v1_relat_1(k1_xboole_0) | ~v1_xboole_0(A_119))), inference(superposition, [status(thm), theory('equality')], [c_415, c_122])).
% 6.21/2.53  tff(c_459, plain, (![A_119]: (~v1_xboole_0(A_119))), inference(negUnitSimplification, [status(thm)], [c_213, c_449])).
% 6.21/2.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.53  tff(c_466, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_459, c_4])).
% 6.21/2.53  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.21/2.53  tff(c_290, plain, (![A_106, C_107, B_108]: (m1_subset_1(A_106, C_107) | ~m1_subset_1(B_108, k1_zfmisc_1(C_107)) | ~r2_hidden(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.53  tff(c_795, plain, (![A_154, B_155, A_156]: (m1_subset_1(A_154, B_155) | ~r2_hidden(A_154, A_156) | ~r1_tarski(A_156, B_155))), inference(resolution, [status(thm)], [c_14, c_290])).
% 6.21/2.53  tff(c_811, plain, (![A_159, B_160]: (m1_subset_1('#skF_1'(A_159), B_160) | ~r1_tarski(A_159, B_160))), inference(resolution, [status(thm)], [c_466, c_795])).
% 6.21/2.53  tff(c_520, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.53  tff(c_543, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_520])).
% 6.21/2.53  tff(c_83, plain, (![A_58]: (v1_xboole_0(A_58) | r2_hidden('#skF_1'(A_58), A_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.53  tff(c_42, plain, (![D_50]: (~r2_hidden(D_50, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.21/2.53  tff(c_91, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_83, c_42])).
% 6.21/2.53  tff(c_123, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_91])).
% 6.21/2.53  tff(c_547, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_543, c_123])).
% 6.21/2.53  tff(c_847, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_811, c_547])).
% 6.21/2.53  tff(c_856, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_847])).
% 6.21/2.53  tff(c_860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_165, c_856])).
% 6.21/2.53  tff(c_861, plain, (![A_89]: (r1_tarski(k1_xboole_0, A_89) | ~v4_relat_1(k1_xboole_0, A_89))), inference(splitRight, [status(thm)], [c_209])).
% 6.21/2.53  tff(c_1823, plain, (![A_270, B_271]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_270, B_271)) | ~v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_1446, c_861])).
% 6.21/2.53  tff(c_164, plain, (![A_9, A_76, B_77]: (v4_relat_1(A_9, A_76) | ~r1_tarski(A_9, k2_zfmisc_1(A_76, B_77)))), inference(resolution, [status(thm)], [c_14, c_152])).
% 6.21/2.53  tff(c_1851, plain, (![A_272]: (v4_relat_1(k1_xboole_0, A_272) | ~v1_xboole_0(A_272))), inference(resolution, [status(thm)], [c_1823, c_164])).
% 6.21/2.53  tff(c_1856, plain, (![A_273]: (r1_tarski(k1_xboole_0, A_273) | ~v1_xboole_0(A_273))), inference(resolution, [status(thm)], [c_1851, c_861])).
% 6.21/2.53  tff(c_863, plain, (![C_161, B_162, A_163]: (~v1_xboole_0(C_161) | ~m1_subset_1(B_162, k1_zfmisc_1(C_161)) | ~r2_hidden(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.21/2.53  tff(c_875, plain, (![B_165, A_166, A_167]: (~v1_xboole_0(B_165) | ~r2_hidden(A_166, A_167) | ~r1_tarski(A_167, B_165))), inference(resolution, [status(thm)], [c_14, c_863])).
% 6.21/2.53  tff(c_880, plain, (![B_165, A_1]: (~v1_xboole_0(B_165) | ~r1_tarski(A_1, B_165) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_875])).
% 6.21/2.53  tff(c_1883, plain, (![A_273]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_273))), inference(resolution, [status(thm)], [c_1856, c_880])).
% 6.21/2.53  tff(c_1889, plain, (![A_273]: (~v1_xboole_0(A_273))), inference(splitLeft, [status(thm)], [c_1883])).
% 6.21/2.53  tff(c_1894, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_1889, c_4])).
% 6.21/2.53  tff(c_1359, plain, (![A_225, C_226, B_227]: (m1_subset_1(A_225, C_226) | ~m1_subset_1(B_227, k1_zfmisc_1(C_226)) | ~r2_hidden(A_225, B_227))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.53  tff(c_2266, plain, (![A_303, B_304, A_305]: (m1_subset_1(A_303, B_304) | ~r2_hidden(A_303, A_305) | ~r1_tarski(A_305, B_304))), inference(resolution, [status(thm)], [c_14, c_1359])).
% 6.21/2.53  tff(c_2273, plain, (![A_306, B_307]: (m1_subset_1('#skF_1'(A_306), B_307) | ~r1_tarski(A_306, B_307))), inference(resolution, [status(thm)], [c_1894, c_2266])).
% 6.21/2.53  tff(c_1953, plain, (![A_278, B_279, C_280]: (k1_relset_1(A_278, B_279, C_280)=k1_relat_1(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.53  tff(c_1976, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1953])).
% 6.21/2.53  tff(c_1979, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_123])).
% 6.21/2.53  tff(c_2314, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2273, c_1979])).
% 6.21/2.53  tff(c_2323, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_2314])).
% 6.21/2.53  tff(c_2327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_165, c_2323])).
% 6.21/2.53  tff(c_2328, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1883])).
% 6.21/2.53  tff(c_956, plain, (![A_177, B_178]: (k2_zfmisc_1(A_177, B_178)=k1_xboole_0 | ~v1_xboole_0(A_177))), inference(resolution, [status(thm)], [c_948, c_81])).
% 6.21/2.53  tff(c_2334, plain, (![B_178]: (k2_zfmisc_1(k1_xboole_0, B_178)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2328, c_956])).
% 6.21/2.53  tff(c_2888, plain, (![A_346, B_347, A_348]: (m1_subset_1(A_346, B_347) | ~r2_hidden(A_346, A_348) | ~r1_tarski(A_348, B_347))), inference(resolution, [status(thm)], [c_14, c_1359])).
% 6.21/2.53  tff(c_3514, plain, (![A_380, B_381]: (m1_subset_1('#skF_2'(A_380), B_381) | ~r1_tarski(A_380, B_381) | k1_xboole_0=A_380)), inference(resolution, [status(thm)], [c_6, c_2888])).
% 6.21/2.53  tff(c_2441, plain, (![A_315, B_316, C_317]: (k1_relset_1(A_315, B_316, C_317)=k1_relat_1(C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.53  tff(c_2470, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_2441])).
% 6.21/2.53  tff(c_80, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_42])).
% 6.21/2.53  tff(c_169, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 6.21/2.53  tff(c_2472, plain, (~m1_subset_1('#skF_2'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2470, c_169])).
% 6.21/2.53  tff(c_3576, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3514, c_2472])).
% 6.21/2.53  tff(c_3641, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3576])).
% 6.21/2.53  tff(c_3644, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_3641])).
% 6.21/2.53  tff(c_3648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_165, c_3644])).
% 6.21/2.53  tff(c_3649, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3576])).
% 6.21/2.53  tff(c_2590, plain, (![D_325, B_326, C_327, A_328]: (m1_subset_1(D_325, k1_zfmisc_1(k2_zfmisc_1(B_326, C_327))) | ~r1_tarski(k1_relat_1(D_325), B_326) | ~m1_subset_1(D_325, k1_zfmisc_1(k2_zfmisc_1(A_328, C_327))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.21/2.53  tff(c_2640, plain, (![B_331]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_331, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_331))), inference(resolution, [status(thm)], [c_46, c_2590])).
% 6.21/2.53  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.21/2.53  tff(c_3129, plain, (![B_360]: (r1_tarski('#skF_5', k2_zfmisc_1(B_360, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_5'), B_360))), inference(resolution, [status(thm)], [c_2640, c_12])).
% 6.21/2.53  tff(c_3148, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_101, c_3129])).
% 6.21/2.53  tff(c_881, plain, (![B_165, A_5]: (~v1_xboole_0(B_165) | ~r1_tarski(A_5, B_165) | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_6, c_875])).
% 6.21/2.53  tff(c_3168, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3148, c_881])).
% 6.21/2.53  tff(c_3176, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_3168])).
% 6.21/2.53  tff(c_3655, plain, (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3649, c_3176])).
% 6.21/2.53  tff(c_3671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2328, c_2334, c_3655])).
% 6.21/2.53  tff(c_3672, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3168])).
% 6.21/2.53  tff(c_2365, plain, (![B_311]: (k2_zfmisc_1(k1_xboole_0, B_311)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2328, c_956])).
% 6.21/2.53  tff(c_2388, plain, (![A_9]: (v4_relat_1(A_9, k1_xboole_0) | ~r1_tarski(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2365, c_164])).
% 6.21/2.53  tff(c_34, plain, (![C_28, A_25, B_26]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.21/2.53  tff(c_2680, plain, (![B_331]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_331) | ~r1_tarski(k1_relat_1('#skF_5'), B_331))), inference(resolution, [status(thm)], [c_2640, c_34])).
% 6.21/2.53  tff(c_2899, plain, (![B_349]: (~v1_xboole_0(B_349) | ~r1_tarski(k1_relat_1('#skF_5'), B_349))), inference(splitLeft, [status(thm)], [c_2680])).
% 6.21/2.53  tff(c_2907, plain, (![A_17]: (~v1_xboole_0(A_17) | ~v4_relat_1('#skF_5', A_17) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_2899])).
% 6.21/2.53  tff(c_2919, plain, (![A_350]: (~v1_xboole_0(A_350) | ~v4_relat_1('#skF_5', A_350))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_2907])).
% 6.21/2.53  tff(c_2930, plain, (~v1_xboole_0(k1_xboole_0) | ~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_2388, c_2919])).
% 6.21/2.53  tff(c_2944, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2328, c_2930])).
% 6.21/2.53  tff(c_3699, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_2944])).
% 6.21/2.53  tff(c_3738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_3699])).
% 6.21/2.53  tff(c_3739, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_2680])).
% 6.21/2.53  tff(c_3746, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3739, c_81])).
% 6.21/2.53  tff(c_2337, plain, (![A_308, B_309, C_310]: (k2_relset_1(A_308, B_309, C_310)=k2_relat_1(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.21/2.53  tff(c_2363, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_2337])).
% 6.21/2.53  tff(c_44, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.21/2.53  tff(c_2427, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_44])).
% 6.21/2.53  tff(c_3761, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3746, c_2427])).
% 6.21/2.53  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.21/2.53  tff(c_3780, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3746, c_3746, c_24])).
% 6.21/2.53  tff(c_3797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3761, c_3780])).
% 6.21/2.53  tff(c_3798, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_80])).
% 6.21/2.53  tff(c_4961, plain, (![A_516, B_517, C_518]: (k1_relset_1(A_516, B_517, C_518)=k1_relat_1(C_518) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.53  tff(c_4979, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_4961])).
% 6.21/2.53  tff(c_4988, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3798, c_4979])).
% 6.21/2.53  tff(c_4999, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17) | ~v4_relat_1('#skF_5', A_17) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4988, c_22])).
% 6.21/2.53  tff(c_5010, plain, (![A_520]: (r1_tarski(k1_xboole_0, A_520) | ~v4_relat_1('#skF_5', A_520))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4999])).
% 6.21/2.53  tff(c_5030, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_165, c_5010])).
% 6.21/2.53  tff(c_4365, plain, (![C_453, A_454, B_455]: (v1_xboole_0(C_453) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~v1_xboole_0(A_454))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.21/2.53  tff(c_4379, plain, (![A_454, B_455]: (v1_xboole_0(k2_zfmisc_1(A_454, B_455)) | ~v1_xboole_0(A_454))), inference(resolution, [status(thm)], [c_51, c_4365])).
% 6.21/2.53  tff(c_4380, plain, (![A_456, B_457]: (v1_xboole_0(k2_zfmisc_1(A_456, B_457)) | ~v1_xboole_0(A_456))), inference(resolution, [status(thm)], [c_51, c_4365])).
% 6.21/2.53  tff(c_4389, plain, (![A_458, B_459]: (k2_zfmisc_1(A_458, B_459)=k1_xboole_0 | ~v1_xboole_0(A_458))), inference(resolution, [status(thm)], [c_4380, c_81])).
% 6.21/2.53  tff(c_4538, plain, (![A_476, B_477, B_478]: (k2_zfmisc_1(k2_zfmisc_1(A_476, B_477), B_478)=k1_xboole_0 | ~v1_xboole_0(A_476))), inference(resolution, [status(thm)], [c_4379, c_4389])).
% 6.21/2.53  tff(c_4952, plain, (![A_514, B_515]: (v4_relat_1(k1_xboole_0, k2_zfmisc_1(A_514, B_515)) | ~v1_xboole_0(A_514))), inference(superposition, [status(thm), theory('equality')], [c_4538, c_166])).
% 6.21/2.53  tff(c_3843, plain, (![B_395, A_396]: (r1_tarski(k1_relat_1(B_395), A_396) | ~v4_relat_1(B_395, A_396) | ~v1_relat_1(B_395))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.21/2.53  tff(c_3858, plain, (![A_396]: (r1_tarski(k1_xboole_0, A_396) | ~v4_relat_1(k1_xboole_0, A_396) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3843])).
% 6.21/2.53  tff(c_3862, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3858])).
% 6.21/2.53  tff(c_3924, plain, (![A_410, C_411, B_412]: (m1_subset_1(A_410, C_411) | ~m1_subset_1(B_412, k1_zfmisc_1(C_411)) | ~r2_hidden(A_410, B_412))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.53  tff(c_4050, plain, (![A_420, B_421, A_422]: (m1_subset_1(A_420, B_421) | ~r2_hidden(A_420, A_422) | ~r1_tarski(A_422, B_421))), inference(resolution, [status(thm)], [c_14, c_3924])).
% 6.21/2.53  tff(c_4057, plain, (![A_423, B_424]: (m1_subset_1('#skF_1'(A_423), B_424) | ~r1_tarski(A_423, B_424) | v1_xboole_0(A_423))), inference(resolution, [status(thm)], [c_4, c_4050])).
% 6.21/2.53  tff(c_3800, plain, (~m1_subset_1('#skF_1'(k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3798, c_123])).
% 6.21/2.53  tff(c_4085, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4057, c_3800])).
% 6.21/2.53  tff(c_4090, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_4085])).
% 6.21/2.53  tff(c_4134, plain, (![A_432, B_433, C_434]: (k1_relset_1(A_432, B_433, C_434)=k1_relat_1(C_434) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.53  tff(c_4153, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_4134])).
% 6.21/2.53  tff(c_4163, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3798, c_4153])).
% 6.21/2.53  tff(c_4174, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17) | ~v4_relat_1('#skF_5', A_17) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4163, c_22])).
% 6.21/2.53  tff(c_4185, plain, (![A_436]: (r1_tarski(k1_xboole_0, A_436) | ~v4_relat_1('#skF_5', A_436))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4174])).
% 6.21/2.53  tff(c_4198, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_165, c_4185])).
% 6.21/2.53  tff(c_4208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4090, c_4198])).
% 6.21/2.53  tff(c_4209, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_4085])).
% 6.21/2.53  tff(c_4216, plain, (![C_437, A_438, B_439]: (v1_xboole_0(C_437) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~v1_xboole_0(A_438))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.21/2.53  tff(c_4255, plain, (![A_440, B_441]: (v1_xboole_0(k2_zfmisc_1(A_440, B_441)) | ~v1_xboole_0(A_440))), inference(resolution, [status(thm)], [c_51, c_4216])).
% 6.21/2.53  tff(c_4264, plain, (![A_442, B_443]: (k2_zfmisc_1(A_442, B_443)=k1_xboole_0 | ~v1_xboole_0(A_442))), inference(resolution, [status(thm)], [c_4255, c_81])).
% 6.21/2.53  tff(c_4271, plain, (![B_444]: (k2_zfmisc_1(k1_xboole_0, B_444)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4209, c_4264])).
% 6.21/2.53  tff(c_4301, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4271, c_122])).
% 6.21/2.53  tff(c_4312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3862, c_4301])).
% 6.21/2.53  tff(c_4313, plain, (![A_396]: (r1_tarski(k1_xboole_0, A_396) | ~v4_relat_1(k1_xboole_0, A_396))), inference(splitRight, [status(thm)], [c_3858])).
% 6.21/2.53  tff(c_5260, plain, (![A_544, B_545]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_544, B_545)) | ~v1_xboole_0(A_544))), inference(resolution, [status(thm)], [c_4952, c_4313])).
% 6.21/2.53  tff(c_5288, plain, (![A_546]: (v4_relat_1(k1_xboole_0, A_546) | ~v1_xboole_0(A_546))), inference(resolution, [status(thm)], [c_5260, c_164])).
% 6.21/2.53  tff(c_5293, plain, (![A_547]: (r1_tarski(k1_xboole_0, A_547) | ~v1_xboole_0(A_547))), inference(resolution, [status(thm)], [c_5288, c_4313])).
% 6.21/2.53  tff(c_4349, plain, (![C_450, B_451, A_452]: (~v1_xboole_0(C_450) | ~m1_subset_1(B_451, k1_zfmisc_1(C_450)) | ~r2_hidden(A_452, B_451))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.21/2.53  tff(c_4393, plain, (![B_460, A_461, A_462]: (~v1_xboole_0(B_460) | ~r2_hidden(A_461, A_462) | ~r1_tarski(A_462, B_460))), inference(resolution, [status(thm)], [c_14, c_4349])).
% 6.21/2.53  tff(c_4398, plain, (![B_460, A_1]: (~v1_xboole_0(B_460) | ~r1_tarski(A_1, B_460) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_4393])).
% 6.21/2.53  tff(c_5320, plain, (![A_547]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_547))), inference(resolution, [status(thm)], [c_5293, c_4398])).
% 6.21/2.53  tff(c_5326, plain, (![A_547]: (~v1_xboole_0(A_547))), inference(splitLeft, [status(thm)], [c_5320])).
% 6.21/2.53  tff(c_5340, plain, (![A_552]: (r2_hidden('#skF_1'(A_552), A_552))), inference(negUnitSimplification, [status(thm)], [c_5326, c_4])).
% 6.21/2.53  tff(c_4426, plain, (![A_467, C_468, B_469]: (m1_subset_1(A_467, C_468) | ~m1_subset_1(B_469, k1_zfmisc_1(C_468)) | ~r2_hidden(A_467, B_469))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.53  tff(c_4433, plain, (![A_467, B_10, A_9]: (m1_subset_1(A_467, B_10) | ~r2_hidden(A_467, A_9) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_4426])).
% 6.21/2.53  tff(c_5452, plain, (![A_558, B_559]: (m1_subset_1('#skF_1'(A_558), B_559) | ~r1_tarski(A_558, B_559))), inference(resolution, [status(thm)], [c_5340, c_4433])).
% 6.21/2.53  tff(c_5469, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_5452, c_3800])).
% 6.21/2.53  tff(c_5493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5030, c_5469])).
% 6.21/2.53  tff(c_5494, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_5320])).
% 6.21/2.53  tff(c_4388, plain, (![A_456, B_457]: (k2_zfmisc_1(A_456, B_457)=k1_xboole_0 | ~v1_xboole_0(A_456))), inference(resolution, [status(thm)], [c_4380, c_81])).
% 6.21/2.53  tff(c_5500, plain, (![B_457]: (k2_zfmisc_1(k1_xboole_0, B_457)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5494, c_4388])).
% 6.21/2.53  tff(c_5220, plain, (![D_539, B_540, C_541, A_542]: (m1_subset_1(D_539, k1_zfmisc_1(k2_zfmisc_1(B_540, C_541))) | ~r1_tarski(k1_relat_1(D_539), B_540) | ~m1_subset_1(D_539, k1_zfmisc_1(k2_zfmisc_1(A_542, C_541))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.21/2.53  tff(c_5233, plain, (![B_540]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_540, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_540))), inference(resolution, [status(thm)], [c_46, c_5220])).
% 6.21/2.53  tff(c_5570, plain, (![B_561]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_561, '#skF_3'))) | ~r1_tarski(k1_xboole_0, B_561))), inference(demodulation, [status(thm), theory('equality')], [c_4988, c_5233])).
% 6.21/2.53  tff(c_5601, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5500, c_5570])).
% 6.21/2.53  tff(c_5621, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5601])).
% 6.21/2.53  tff(c_18, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.21/2.53  tff(c_5625, plain, (![A_14]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_14, '#skF_5'))), inference(resolution, [status(thm)], [c_5621, c_18])).
% 6.21/2.53  tff(c_5634, plain, (![A_562]: (~r2_hidden(A_562, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5494, c_5625])).
% 6.21/2.53  tff(c_5644, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_6, c_5634])).
% 6.21/2.53  tff(c_5683, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5644, c_5644, c_24])).
% 6.21/2.53  tff(c_5039, plain, (![A_521, B_522, C_523]: (k2_relset_1(A_521, B_522, C_523)=k2_relat_1(C_523) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.21/2.53  tff(c_5065, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_5039])).
% 6.21/2.53  tff(c_5067, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5065, c_44])).
% 6.21/2.53  tff(c_5660, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5644, c_5067])).
% 6.21/2.53  tff(c_5723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5683, c_5660])).
% 6.21/2.53  tff(c_5724, plain, (v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_91])).
% 6.21/2.53  tff(c_5730, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_5724, c_81])).
% 6.21/2.53  tff(c_5731, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5730, c_5724])).
% 6.21/2.53  tff(c_6244, plain, (![C_646, A_647, B_648]: (v1_xboole_0(C_646) | ~m1_subset_1(C_646, k1_zfmisc_1(k2_zfmisc_1(A_647, B_648))) | ~v1_xboole_0(A_647))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.21/2.53  tff(c_6268, plain, (![A_651, B_652]: (v1_xboole_0(k2_zfmisc_1(A_651, B_652)) | ~v1_xboole_0(A_651))), inference(resolution, [status(thm)], [c_51, c_6244])).
% 6.21/2.53  tff(c_6346, plain, (![A_656, B_657]: (k2_zfmisc_1(A_656, B_657)=k1_xboole_0 | ~v1_xboole_0(A_656))), inference(resolution, [status(thm)], [c_6268, c_81])).
% 6.21/2.53  tff(c_6352, plain, (![B_657]: (k2_zfmisc_1(k1_xboole_0, B_657)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5731, c_6346])).
% 6.21/2.53  tff(c_6547, plain, (![A_673, B_674, C_675]: (k1_relset_1(A_673, B_674, C_675)=k1_relat_1(C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(A_673, B_674))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.53  tff(c_6565, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_6547])).
% 6.21/2.53  tff(c_6574, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5730, c_6565])).
% 6.21/2.53  tff(c_6929, plain, (![D_688, B_689, C_690, A_691]: (m1_subset_1(D_688, k1_zfmisc_1(k2_zfmisc_1(B_689, C_690))) | ~r1_tarski(k1_relat_1(D_688), B_689) | ~m1_subset_1(D_688, k1_zfmisc_1(k2_zfmisc_1(A_691, C_690))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.21/2.53  tff(c_6942, plain, (![B_689]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_689, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_689))), inference(resolution, [status(thm)], [c_46, c_6929])).
% 6.21/2.53  tff(c_6972, plain, (![B_693]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_693, '#skF_3'))) | ~r1_tarski(k1_xboole_0, B_693))), inference(demodulation, [status(thm), theory('equality')], [c_6574, c_6942])).
% 6.21/2.53  tff(c_7003, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6352, c_6972])).
% 6.21/2.53  tff(c_7019, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_7003])).
% 6.21/2.53  tff(c_6353, plain, (![B_658]: (k2_zfmisc_1(k1_xboole_0, B_658)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5731, c_6346])).
% 6.21/2.53  tff(c_6361, plain, (![C_28]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6353, c_34])).
% 6.21/2.53  tff(c_6392, plain, (![C_28]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_5731, c_6361])).
% 6.21/2.53  tff(c_7041, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_7019, c_6392])).
% 6.21/2.53  tff(c_7055, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7041, c_81])).
% 6.21/2.53  tff(c_6409, plain, (![A_661, B_662, C_663]: (k2_relset_1(A_661, B_662, C_663)=k2_relat_1(C_663) | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(A_661, B_662))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.21/2.53  tff(c_6435, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_6409])).
% 6.21/2.53  tff(c_6437, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6435, c_44])).
% 6.21/2.53  tff(c_7075, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7055, c_6437])).
% 6.21/2.53  tff(c_7092, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7055, c_7055, c_24])).
% 6.21/2.53  tff(c_7132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7075, c_7092])).
% 6.21/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.53  
% 6.21/2.53  Inference rules
% 6.21/2.53  ----------------------
% 6.21/2.53  #Ref     : 0
% 6.21/2.53  #Sup     : 1466
% 6.21/2.53  #Fact    : 0
% 6.21/2.53  #Define  : 0
% 6.21/2.53  #Split   : 27
% 6.21/2.53  #Chain   : 0
% 6.21/2.53  #Close   : 0
% 6.21/2.53  
% 6.21/2.53  Ordering : KBO
% 6.21/2.53  
% 6.21/2.53  Simplification rules
% 6.21/2.53  ----------------------
% 6.21/2.53  #Subsume      : 254
% 6.21/2.53  #Demod        : 749
% 6.21/2.53  #Tautology    : 390
% 6.21/2.53  #SimpNegUnit  : 56
% 6.21/2.53  #BackRed      : 264
% 6.21/2.53  
% 6.21/2.53  #Partial instantiations: 0
% 6.21/2.53  #Strategies tried      : 1
% 6.21/2.53  
% 6.21/2.53  Timing (in seconds)
% 6.21/2.53  ----------------------
% 6.21/2.54  Preprocessing        : 0.42
% 6.21/2.54  Parsing              : 0.23
% 6.21/2.54  CNF conversion       : 0.03
% 6.21/2.54  Main loop            : 1.13
% 6.21/2.54  Inferencing          : 0.40
% 6.21/2.54  Reduction            : 0.36
% 6.21/2.54  Demodulation         : 0.24
% 6.21/2.54  BG Simplification    : 0.04
% 6.21/2.54  Subsumption          : 0.21
% 6.21/2.54  Abstraction          : 0.05
% 6.21/2.54  MUC search           : 0.00
% 6.21/2.54  Cooper               : 0.00
% 6.21/2.54  Total                : 1.63
% 6.21/2.54  Index Insertion      : 0.00
% 6.21/2.54  Index Deletion       : 0.00
% 6.21/2.54  Index Matching       : 0.00
% 6.21/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
