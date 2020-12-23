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
% DateTime   : Thu Dec  3 09:57:07 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 263 expanded)
%              Number of leaves         :   24 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  161 ( 603 expanded)
%              Number of equality atoms :    9 (  39 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_85,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_52,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_10,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_105,plain,(
    ! [A_13] :
      ( r2_hidden(A_13,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k1_tarski(A_13),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_97,c_10])).

tff(c_106,plain,(
    ! [A_53] :
      ( r2_hidden(A_53,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k1_tarski(A_53),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_97,c_10])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k1_tarski(A_53),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_120,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ r2_hidden(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_118,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,k2_zfmisc_1('#skF_4','#skF_5'))
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k1_tarski(A_53),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_106,c_20])).

tff(c_369,plain,(
    ! [A_107] :
      ( m1_subset_1(A_107,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k1_tarski(A_107),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_118])).

tff(c_374,plain,(
    ! [A_13] :
      ( m1_subset_1(A_13,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_13,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_369])).

tff(c_232,plain,(
    ! [A_88,B_89,C_90] :
      ( k4_tarski('#skF_2'(A_88,B_89,C_90),'#skF_3'(A_88,B_89,C_90)) = A_88
      | ~ r2_hidden(A_88,k2_zfmisc_1(B_89,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_149,plain,(
    ! [B_62,D_63,A_64,C_65] :
      ( r2_hidden(B_62,D_63)
      | ~ r2_hidden(k4_tarski(A_64,B_62),k2_zfmisc_1(C_65,D_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_176,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,'#skF_5')
      | ~ r1_tarski(k1_tarski(k4_tarski(A_71,B_70)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_149])).

tff(c_180,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_71,B_70),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_176])).

tff(c_584,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_3'(A_129,B_130,C_131),'#skF_5')
      | ~ r2_hidden(A_129,'#skF_6')
      | ~ r2_hidden(A_129,k2_zfmisc_1(B_130,C_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_180])).

tff(c_598,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_129,'#skF_6')
      | ~ r2_hidden(A_129,k2_zfmisc_1(B_130,C_131)) ) ),
    inference(resolution,[status(thm)],[c_584,c_2])).

tff(c_625,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_598])).

tff(c_16,plain,(
    ! [B_16,D_18,A_15,C_17] :
      ( r2_hidden(B_16,D_18)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_599,plain,(
    ! [C_132,C_136,D_133,B_134,A_135] :
      ( r2_hidden('#skF_3'(A_135,B_134,C_136),D_133)
      | ~ r2_hidden(A_135,k2_zfmisc_1(C_132,D_133))
      | ~ r2_hidden(A_135,k2_zfmisc_1(B_134,C_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_16])).

tff(c_811,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden('#skF_3'(A_159,B_160,C_161),'#skF_5')
      | ~ r2_hidden(A_159,k2_zfmisc_1(B_160,C_161))
      | ~ r1_tarski(k1_tarski(A_159),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_599])).

tff(c_818,plain,(
    ! [A_159,B_160,C_161] :
      ( m1_subset_1('#skF_3'(A_159,B_160,C_161),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_159,k2_zfmisc_1(B_160,C_161))
      | ~ r1_tarski(k1_tarski(A_159),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_811,c_20])).

tff(c_871,plain,(
    ! [A_168,B_169,C_170] :
      ( m1_subset_1('#skF_3'(A_168,B_169,C_170),'#skF_5')
      | ~ r2_hidden(A_168,k2_zfmisc_1(B_169,C_170))
      | ~ r1_tarski(k1_tarski(A_168),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_625,c_818])).

tff(c_920,plain,(
    ! [A_175] :
      ( m1_subset_1('#skF_3'(A_175,'#skF_4','#skF_5'),'#skF_5')
      | ~ r1_tarski(k1_tarski(A_175),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_871])).

tff(c_939,plain,(
    ! [A_13] :
      ( m1_subset_1('#skF_3'(A_13,'#skF_4','#skF_5'),'#skF_5')
      | ~ r2_hidden(A_13,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_920])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16,D_18] :
      ( r2_hidden(A_15,C_17)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_132,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,'#skF_4')
      | ~ r1_tarski(k1_tarski(k4_tarski(A_56,B_57)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_106,c_18])).

tff(c_136,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_56,B_57),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_568,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden('#skF_2'(A_126,B_127,C_128),'#skF_4')
      | ~ r2_hidden(A_126,'#skF_6')
      | ~ r2_hidden(A_126,k2_zfmisc_1(B_127,C_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_136])).

tff(c_582,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_126,'#skF_6')
      | ~ r2_hidden(A_126,k2_zfmisc_1(B_127,C_128)) ) ),
    inference(resolution,[status(thm)],[c_568,c_2])).

tff(c_583,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_582])).

tff(c_760,plain,(
    ! [C_152,A_155,D_153,C_156,B_154] :
      ( r2_hidden('#skF_2'(A_155,B_154,C_156),C_152)
      | ~ r2_hidden(A_155,k2_zfmisc_1(C_152,D_153))
      | ~ r2_hidden(A_155,k2_zfmisc_1(B_154,C_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_18])).

tff(c_833,plain,(
    ! [A_163,B_164,C_165] :
      ( r2_hidden('#skF_2'(A_163,B_164,C_165),'#skF_4')
      | ~ r2_hidden(A_163,k2_zfmisc_1(B_164,C_165))
      | ~ r1_tarski(k1_tarski(A_163),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_760])).

tff(c_840,plain,(
    ! [A_163,B_164,C_165] :
      ( m1_subset_1('#skF_2'(A_163,B_164,C_165),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_163,k2_zfmisc_1(B_164,C_165))
      | ~ r1_tarski(k1_tarski(A_163),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_833,c_20])).

tff(c_959,plain,(
    ! [A_179,B_180,C_181] :
      ( m1_subset_1('#skF_2'(A_179,B_180,C_181),'#skF_4')
      | ~ r2_hidden(A_179,k2_zfmisc_1(B_180,C_181))
      | ~ r1_tarski(k1_tarski(A_179),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_840])).

tff(c_992,plain,(
    ! [A_182] :
      ( m1_subset_1('#skF_2'(A_182,'#skF_4','#skF_5'),'#skF_4')
      | ~ r1_tarski(k1_tarski(A_182),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_959])).

tff(c_1011,plain,(
    ! [A_13] :
      ( m1_subset_1('#skF_2'(A_13,'#skF_4','#skF_5'),'#skF_4')
      | ~ r2_hidden(A_13,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_992])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(B_20,A_19)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [E_24,F_26] :
      ( k4_tarski(E_24,F_26) != '#skF_7'
      | ~ m1_subset_1(F_26,'#skF_5')
      | ~ m1_subset_1(E_24,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_283,plain,(
    ! [A_92,B_93,C_94] :
      ( A_92 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_92,B_93,C_94),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_92,B_93,C_94),'#skF_4')
      | ~ r2_hidden(A_92,k2_zfmisc_1(B_93,C_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_28])).

tff(c_1149,plain,(
    ! [B_198,B_199,C_200] :
      ( B_198 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(B_198,B_199,C_200),'#skF_5')
      | ~ m1_subset_1('#skF_2'(B_198,B_199,C_200),'#skF_4')
      | ~ m1_subset_1(B_198,k2_zfmisc_1(B_199,C_200))
      | v1_xboole_0(k2_zfmisc_1(B_199,C_200)) ) ),
    inference(resolution,[status(thm)],[c_22,c_283])).

tff(c_1155,plain,(
    ! [A_13] :
      ( A_13 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_13,'#skF_4','#skF_5'),'#skF_5')
      | ~ m1_subset_1(A_13,k2_zfmisc_1('#skF_4','#skF_5'))
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_13,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1011,c_1149])).

tff(c_1393,plain,(
    ! [A_220] :
      ( A_220 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_220,'#skF_4','#skF_5'),'#skF_5')
      | ~ m1_subset_1(A_220,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_220,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1155])).

tff(c_1407,plain,(
    ! [A_221] :
      ( A_221 != '#skF_7'
      | ~ m1_subset_1(A_221,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_221,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_939,c_1393])).

tff(c_1457,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_374,c_1407])).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1457,c_32])).

tff(c_1462,plain,(
    ! [A_222,B_223,C_224] :
      ( ~ r2_hidden(A_222,'#skF_6')
      | ~ r2_hidden(A_222,k2_zfmisc_1(B_223,C_224)) ) ),
    inference(splitRight,[status(thm)],[c_598])).

tff(c_1521,plain,(
    ! [A_230] :
      ( ~ r2_hidden(A_230,'#skF_6')
      | ~ r1_tarski(k1_tarski(A_230),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_1462])).

tff(c_1540,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1521])).

tff(c_1542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1540,c_32])).

tff(c_1552,plain,(
    ! [A_232,B_233,C_234] :
      ( ~ r2_hidden(A_232,'#skF_6')
      | ~ r2_hidden(A_232,k2_zfmisc_1(B_233,C_234)) ) ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_1585,plain,(
    ! [A_235] :
      ( ~ r2_hidden(A_235,'#skF_6')
      | ~ r1_tarski(k1_tarski(A_235),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_1552])).

tff(c_1604,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1585])).

tff(c_1606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1604,c_32])).

tff(c_1609,plain,(
    ! [A_236] : ~ r1_tarski(k1_tarski(A_236),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1614,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1609])).

tff(c_1616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1614,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.61  
% 3.49/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.61  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.49/1.61  
% 3.49/1.61  %Foreground sorts:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Background operators:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Foreground operators:
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.49/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.61  
% 3.83/1.63  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.83/1.63  tff(f_82, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_subset_1)).
% 3.83/1.63  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.83/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.83/1.63  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.83/1.63  tff(f_44, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.83/1.63  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.83/1.63  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.83/1.63  tff(c_30, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/1.63  tff(c_85, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.63  tff(c_97, plain, (![A_52]: (r1_tarski(A_52, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_52, '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_85])).
% 3.83/1.63  tff(c_10, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.83/1.63  tff(c_105, plain, (![A_13]: (r2_hidden(A_13, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski(A_13), '#skF_6'))), inference(resolution, [status(thm)], [c_97, c_10])).
% 3.83/1.63  tff(c_106, plain, (![A_53]: (r2_hidden(A_53, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski(A_53), '#skF_6'))), inference(resolution, [status(thm)], [c_97, c_10])).
% 3.83/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.63  tff(c_119, plain, (![A_53]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski(A_53), '#skF_6'))), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.83/1.63  tff(c_120, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_119])).
% 3.83/1.63  tff(c_20, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~r2_hidden(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.83/1.63  tff(c_118, plain, (![A_53]: (m1_subset_1(A_53, k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski(A_53), '#skF_6'))), inference(resolution, [status(thm)], [c_106, c_20])).
% 3.83/1.63  tff(c_369, plain, (![A_107]: (m1_subset_1(A_107, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski(A_107), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_120, c_118])).
% 3.83/1.63  tff(c_374, plain, (![A_13]: (m1_subset_1(A_13, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_369])).
% 3.83/1.63  tff(c_232, plain, (![A_88, B_89, C_90]: (k4_tarski('#skF_2'(A_88, B_89, C_90), '#skF_3'(A_88, B_89, C_90))=A_88 | ~r2_hidden(A_88, k2_zfmisc_1(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.83/1.63  tff(c_149, plain, (![B_62, D_63, A_64, C_65]: (r2_hidden(B_62, D_63) | ~r2_hidden(k4_tarski(A_64, B_62), k2_zfmisc_1(C_65, D_63)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/1.63  tff(c_176, plain, (![B_70, A_71]: (r2_hidden(B_70, '#skF_5') | ~r1_tarski(k1_tarski(k4_tarski(A_71, B_70)), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_149])).
% 3.83/1.63  tff(c_180, plain, (![B_70, A_71]: (r2_hidden(B_70, '#skF_5') | ~r2_hidden(k4_tarski(A_71, B_70), '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_176])).
% 3.83/1.63  tff(c_584, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_3'(A_129, B_130, C_131), '#skF_5') | ~r2_hidden(A_129, '#skF_6') | ~r2_hidden(A_129, k2_zfmisc_1(B_130, C_131)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_180])).
% 3.83/1.63  tff(c_598, plain, (![A_129, B_130, C_131]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_129, '#skF_6') | ~r2_hidden(A_129, k2_zfmisc_1(B_130, C_131)))), inference(resolution, [status(thm)], [c_584, c_2])).
% 3.83/1.63  tff(c_625, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_598])).
% 3.83/1.63  tff(c_16, plain, (![B_16, D_18, A_15, C_17]: (r2_hidden(B_16, D_18) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/1.63  tff(c_599, plain, (![C_132, C_136, D_133, B_134, A_135]: (r2_hidden('#skF_3'(A_135, B_134, C_136), D_133) | ~r2_hidden(A_135, k2_zfmisc_1(C_132, D_133)) | ~r2_hidden(A_135, k2_zfmisc_1(B_134, C_136)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_16])).
% 3.83/1.63  tff(c_811, plain, (![A_159, B_160, C_161]: (r2_hidden('#skF_3'(A_159, B_160, C_161), '#skF_5') | ~r2_hidden(A_159, k2_zfmisc_1(B_160, C_161)) | ~r1_tarski(k1_tarski(A_159), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_599])).
% 3.83/1.63  tff(c_818, plain, (![A_159, B_160, C_161]: (m1_subset_1('#skF_3'(A_159, B_160, C_161), '#skF_5') | v1_xboole_0('#skF_5') | ~r2_hidden(A_159, k2_zfmisc_1(B_160, C_161)) | ~r1_tarski(k1_tarski(A_159), '#skF_6'))), inference(resolution, [status(thm)], [c_811, c_20])).
% 3.83/1.63  tff(c_871, plain, (![A_168, B_169, C_170]: (m1_subset_1('#skF_3'(A_168, B_169, C_170), '#skF_5') | ~r2_hidden(A_168, k2_zfmisc_1(B_169, C_170)) | ~r1_tarski(k1_tarski(A_168), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_625, c_818])).
% 3.83/1.63  tff(c_920, plain, (![A_175]: (m1_subset_1('#skF_3'(A_175, '#skF_4', '#skF_5'), '#skF_5') | ~r1_tarski(k1_tarski(A_175), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_871])).
% 3.83/1.63  tff(c_939, plain, (![A_13]: (m1_subset_1('#skF_3'(A_13, '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_920])).
% 3.83/1.63  tff(c_18, plain, (![A_15, C_17, B_16, D_18]: (r2_hidden(A_15, C_17) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/1.63  tff(c_132, plain, (![A_56, B_57]: (r2_hidden(A_56, '#skF_4') | ~r1_tarski(k1_tarski(k4_tarski(A_56, B_57)), '#skF_6'))), inference(resolution, [status(thm)], [c_106, c_18])).
% 3.83/1.63  tff(c_136, plain, (![A_56, B_57]: (r2_hidden(A_56, '#skF_4') | ~r2_hidden(k4_tarski(A_56, B_57), '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_132])).
% 3.83/1.63  tff(c_568, plain, (![A_126, B_127, C_128]: (r2_hidden('#skF_2'(A_126, B_127, C_128), '#skF_4') | ~r2_hidden(A_126, '#skF_6') | ~r2_hidden(A_126, k2_zfmisc_1(B_127, C_128)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_136])).
% 3.83/1.63  tff(c_582, plain, (![A_126, B_127, C_128]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_126, '#skF_6') | ~r2_hidden(A_126, k2_zfmisc_1(B_127, C_128)))), inference(resolution, [status(thm)], [c_568, c_2])).
% 3.83/1.63  tff(c_583, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_582])).
% 3.83/1.63  tff(c_760, plain, (![C_152, A_155, D_153, C_156, B_154]: (r2_hidden('#skF_2'(A_155, B_154, C_156), C_152) | ~r2_hidden(A_155, k2_zfmisc_1(C_152, D_153)) | ~r2_hidden(A_155, k2_zfmisc_1(B_154, C_156)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_18])).
% 3.83/1.63  tff(c_833, plain, (![A_163, B_164, C_165]: (r2_hidden('#skF_2'(A_163, B_164, C_165), '#skF_4') | ~r2_hidden(A_163, k2_zfmisc_1(B_164, C_165)) | ~r1_tarski(k1_tarski(A_163), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_760])).
% 3.83/1.63  tff(c_840, plain, (![A_163, B_164, C_165]: (m1_subset_1('#skF_2'(A_163, B_164, C_165), '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden(A_163, k2_zfmisc_1(B_164, C_165)) | ~r1_tarski(k1_tarski(A_163), '#skF_6'))), inference(resolution, [status(thm)], [c_833, c_20])).
% 3.83/1.63  tff(c_959, plain, (![A_179, B_180, C_181]: (m1_subset_1('#skF_2'(A_179, B_180, C_181), '#skF_4') | ~r2_hidden(A_179, k2_zfmisc_1(B_180, C_181)) | ~r1_tarski(k1_tarski(A_179), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_583, c_840])).
% 3.83/1.63  tff(c_992, plain, (![A_182]: (m1_subset_1('#skF_2'(A_182, '#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski(A_182), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_959])).
% 3.83/1.63  tff(c_1011, plain, (![A_13]: (m1_subset_1('#skF_2'(A_13, '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_992])).
% 3.83/1.63  tff(c_22, plain, (![B_20, A_19]: (r2_hidden(B_20, A_19) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.83/1.63  tff(c_28, plain, (![E_24, F_26]: (k4_tarski(E_24, F_26)!='#skF_7' | ~m1_subset_1(F_26, '#skF_5') | ~m1_subset_1(E_24, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/1.63  tff(c_283, plain, (![A_92, B_93, C_94]: (A_92!='#skF_7' | ~m1_subset_1('#skF_3'(A_92, B_93, C_94), '#skF_5') | ~m1_subset_1('#skF_2'(A_92, B_93, C_94), '#skF_4') | ~r2_hidden(A_92, k2_zfmisc_1(B_93, C_94)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_28])).
% 3.83/1.63  tff(c_1149, plain, (![B_198, B_199, C_200]: (B_198!='#skF_7' | ~m1_subset_1('#skF_3'(B_198, B_199, C_200), '#skF_5') | ~m1_subset_1('#skF_2'(B_198, B_199, C_200), '#skF_4') | ~m1_subset_1(B_198, k2_zfmisc_1(B_199, C_200)) | v1_xboole_0(k2_zfmisc_1(B_199, C_200)))), inference(resolution, [status(thm)], [c_22, c_283])).
% 3.83/1.63  tff(c_1155, plain, (![A_13]: (A_13!='#skF_7' | ~m1_subset_1('#skF_3'(A_13, '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1(A_13, k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_1011, c_1149])).
% 3.83/1.63  tff(c_1393, plain, (![A_220]: (A_220!='#skF_7' | ~m1_subset_1('#skF_3'(A_220, '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1(A_220, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_220, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_120, c_1155])).
% 3.83/1.63  tff(c_1407, plain, (![A_221]: (A_221!='#skF_7' | ~m1_subset_1(A_221, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_221, '#skF_6'))), inference(resolution, [status(thm)], [c_939, c_1393])).
% 3.83/1.63  tff(c_1457, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_374, c_1407])).
% 3.83/1.63  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/1.63  tff(c_1459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1457, c_32])).
% 3.83/1.63  tff(c_1462, plain, (![A_222, B_223, C_224]: (~r2_hidden(A_222, '#skF_6') | ~r2_hidden(A_222, k2_zfmisc_1(B_223, C_224)))), inference(splitRight, [status(thm)], [c_598])).
% 3.83/1.63  tff(c_1521, plain, (![A_230]: (~r2_hidden(A_230, '#skF_6') | ~r1_tarski(k1_tarski(A_230), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_1462])).
% 3.83/1.63  tff(c_1540, plain, (![A_13]: (~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_1521])).
% 3.83/1.63  tff(c_1542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1540, c_32])).
% 3.83/1.63  tff(c_1552, plain, (![A_232, B_233, C_234]: (~r2_hidden(A_232, '#skF_6') | ~r2_hidden(A_232, k2_zfmisc_1(B_233, C_234)))), inference(splitRight, [status(thm)], [c_582])).
% 3.83/1.63  tff(c_1585, plain, (![A_235]: (~r2_hidden(A_235, '#skF_6') | ~r1_tarski(k1_tarski(A_235), '#skF_6'))), inference(resolution, [status(thm)], [c_105, c_1552])).
% 3.83/1.63  tff(c_1604, plain, (![A_13]: (~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_1585])).
% 3.83/1.63  tff(c_1606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1604, c_32])).
% 3.83/1.63  tff(c_1609, plain, (![A_236]: (~r1_tarski(k1_tarski(A_236), '#skF_6'))), inference(splitRight, [status(thm)], [c_119])).
% 3.83/1.63  tff(c_1614, plain, (![A_13]: (~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_1609])).
% 3.83/1.63  tff(c_1616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1614, c_32])).
% 3.83/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.63  
% 3.83/1.63  Inference rules
% 3.83/1.63  ----------------------
% 3.83/1.63  #Ref     : 0
% 3.83/1.63  #Sup     : 338
% 3.83/1.63  #Fact    : 0
% 3.83/1.63  #Define  : 0
% 3.83/1.63  #Split   : 6
% 3.83/1.63  #Chain   : 0
% 3.83/1.63  #Close   : 0
% 3.83/1.63  
% 3.83/1.63  Ordering : KBO
% 3.83/1.63  
% 3.83/1.63  Simplification rules
% 3.83/1.63  ----------------------
% 3.83/1.63  #Subsume      : 72
% 3.83/1.63  #Demod        : 13
% 3.83/1.63  #Tautology    : 35
% 3.83/1.63  #SimpNegUnit  : 55
% 3.83/1.63  #BackRed      : 4
% 3.83/1.63  
% 3.83/1.63  #Partial instantiations: 0
% 3.83/1.63  #Strategies tried      : 1
% 3.83/1.63  
% 3.83/1.63  Timing (in seconds)
% 3.83/1.63  ----------------------
% 3.83/1.64  Preprocessing        : 0.28
% 3.83/1.64  Parsing              : 0.15
% 3.83/1.64  CNF conversion       : 0.02
% 3.83/1.64  Main loop            : 0.57
% 3.83/1.64  Inferencing          : 0.21
% 3.83/1.64  Reduction            : 0.14
% 3.83/1.64  Demodulation         : 0.08
% 3.83/1.64  BG Simplification    : 0.03
% 3.83/1.64  Subsumption          : 0.15
% 3.83/1.64  Abstraction          : 0.02
% 3.83/1.64  MUC search           : 0.00
% 3.83/1.64  Cooper               : 0.00
% 3.83/1.64  Total                : 0.89
% 3.83/1.64  Index Insertion      : 0.00
% 3.83/1.64  Index Deletion       : 0.00
% 3.83/1.64  Index Matching       : 0.00
% 3.83/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
