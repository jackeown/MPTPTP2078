%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:24 EST 2020

% Result     : Theorem 14.32s
% Output     : CNFRefutation 14.32s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 246 expanded)
%              Number of leaves         :   41 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 600 expanded)
%              Number of equality atoms :   61 ( 150 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_104,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_122,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_62,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3'(A_40),A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_196,plain,(
    ! [C_104,A_105,B_106] :
      ( r2_hidden(C_104,A_105)
      | ~ r2_hidden(C_104,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [A_107,A_108] :
      ( r2_hidden('#skF_3'(A_107),A_108)
      | ~ m1_subset_1(A_107,k1_zfmisc_1(A_108))
      | k1_xboole_0 = A_107 ) ),
    inference(resolution,[status(thm)],[c_40,c_196])).

tff(c_30,plain,(
    ! [A_34,C_36,B_35] :
      ( r2_hidden(k2_mcart_1(A_34),C_36)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_431,plain,(
    ! [A_131,C_132,B_133] :
      ( r2_hidden(k2_mcart_1('#skF_3'(A_131)),C_132)
      | ~ m1_subset_1(A_131,k1_zfmisc_1(k2_zfmisc_1(B_133,C_132)))
      | k1_xboole_0 = A_131 ) ),
    inference(resolution,[status(thm)],[c_200,c_30])).

tff(c_442,plain,
    ( r2_hidden(k2_mcart_1('#skF_3'('#skF_6')),'#skF_5')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_431])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(A_82,B_83)
      | k4_xboole_0(k1_tarski(A_82),B_83) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_143,plain,(
    ! [A_85] :
      ( r2_hidden(A_85,k1_xboole_0)
      | k1_tarski(A_85) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,(
    ! [A_85] :
      ( ~ r1_tarski(k1_xboole_0,A_85)
      | k1_tarski(A_85) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_143,c_22])).

tff(c_153,plain,(
    ! [A_85] : k1_tarski(A_85) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_460,plain,(
    ! [A_85] : k1_tarski(A_85) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_153])).

tff(c_483,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden('#skF_1'(A_139,B_140,C_141),B_140)
      | k1_relset_1(B_140,A_139,C_141) = B_140
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(B_140,A_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_486,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_4'),'#skF_6'),k1_tarski('#skF_4'))
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_483])).

tff(c_607,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_465,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3'(A_40),A_40)
      | A_40 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_40])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_467,plain,(
    ! [A_15] : m1_subset_1('#skF_6',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_18])).

tff(c_833,plain,(
    ! [D_189,A_190,B_191,C_192] :
      ( r2_hidden(k4_tarski(D_189,'#skF_2'(A_190,B_191,C_192,D_189)),C_192)
      | ~ r2_hidden(D_189,B_191)
      | k1_relset_1(B_191,A_190,C_192) != B_191
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(B_191,A_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_110,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(k1_tarski(A_80),B_81) = k1_xboole_0
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_80] :
      ( k1_tarski(A_80) = k1_xboole_0
      | ~ r2_hidden(A_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_4])).

tff(c_163,plain,(
    ! [A_80] : ~ r2_hidden(A_80,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_117])).

tff(c_459,plain,(
    ! [A_80] : ~ r2_hidden(A_80,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_163])).

tff(c_846,plain,(
    ! [D_189,B_191,A_190] :
      ( ~ r2_hidden(D_189,B_191)
      | k1_relset_1(B_191,A_190,'#skF_6') != B_191
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_191,A_190))) ) ),
    inference(resolution,[status(thm)],[c_833,c_459])).

tff(c_873,plain,(
    ! [D_193,B_194,A_195] :
      ( ~ r2_hidden(D_193,B_194)
      | k1_relset_1(B_194,A_195,'#skF_6') != B_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_846])).

tff(c_889,plain,(
    ! [A_196,A_197] :
      ( k1_relset_1(A_196,A_197,'#skF_6') != A_196
      | A_196 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_465,c_873])).

tff(c_895,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_889])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_895])).

tff(c_903,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_469,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_58])).

tff(c_52,plain,(
    ! [B_63,A_62,C_64] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_62,B_63,C_64) = A_62
      | ~ v1_funct_2(C_64,A_62,B_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_559,plain,(
    ! [B_147,A_148,C_149] :
      ( B_147 = '#skF_6'
      | k1_relset_1(A_148,B_147,C_149) = A_148
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_52])).

tff(c_1175,plain,(
    ! [B_238,A_239] :
      ( B_238 = '#skF_6'
      | k1_relset_1(A_239,B_238,'#skF_6') = A_239
      | ~ v1_funct_2('#skF_6',A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_467,c_559])).

tff(c_1187,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1175])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_469,c_1187])).

tff(c_1198,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_36,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_mcart_1(A_37) = B_38
      | ~ r2_hidden(A_37,k2_zfmisc_1(k1_tarski(B_38),C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1285,plain,(
    ! [A_255,B_256,C_257] :
      ( k1_mcart_1('#skF_3'(A_255)) = B_256
      | ~ m1_subset_1(A_255,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_256),C_257)))
      | k1_xboole_0 = A_255 ) ),
    inference(resolution,[status(thm)],[c_200,c_36])).

tff(c_1291,plain,
    ( k1_mcart_1('#skF_3'('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_1285])).

tff(c_1298,plain,(
    k1_mcart_1('#skF_3'('#skF_6')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1198,c_1291])).

tff(c_32,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k1_mcart_1(A_34),B_35)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1305,plain,(
    ! [A_258,B_259,C_260] :
      ( r2_hidden(k1_mcart_1('#skF_3'(A_258)),B_259)
      | ~ m1_subset_1(A_258,k1_zfmisc_1(k2_zfmisc_1(B_259,C_260)))
      | k1_xboole_0 = A_258 ) ),
    inference(resolution,[status(thm)],[c_200,c_32])).

tff(c_1311,plain,
    ( r2_hidden(k1_mcart_1('#skF_3'('#skF_6')),k1_tarski('#skF_4'))
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_1305])).

tff(c_1317,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_1311])).

tff(c_1318,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1198,c_1317])).

tff(c_1827,plain,(
    ! [D_326,C_327,B_328,A_329] :
      ( r2_hidden(k1_funct_1(D_326,C_327),B_328)
      | k1_xboole_0 = B_328
      | ~ r2_hidden(C_327,A_329)
      | ~ m1_subset_1(D_326,k1_zfmisc_1(k2_zfmisc_1(A_329,B_328)))
      | ~ v1_funct_2(D_326,A_329,B_328)
      | ~ v1_funct_1(D_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34210,plain,(
    ! [D_1857,B_1858] :
      ( r2_hidden(k1_funct_1(D_1857,'#skF_4'),B_1858)
      | k1_xboole_0 = B_1858
      | ~ m1_subset_1(D_1857,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),B_1858)))
      | ~ v1_funct_2(D_1857,k1_tarski('#skF_4'),B_1858)
      | ~ v1_funct_1(D_1857) ) ),
    inference(resolution,[status(thm)],[c_1318,c_1827])).

tff(c_34257,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_34210])).

tff(c_34267,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_34257])).

tff(c_34269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_34267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.32/7.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.32/7.71  
% 14.32/7.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.32/7.71  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 14.32/7.71  
% 14.32/7.71  %Foreground sorts:
% 14.32/7.71  
% 14.32/7.71  
% 14.32/7.71  %Background operators:
% 14.32/7.71  
% 14.32/7.71  
% 14.32/7.71  %Foreground operators:
% 14.32/7.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.32/7.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.32/7.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.32/7.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.32/7.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.32/7.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.32/7.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.32/7.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.32/7.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.32/7.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.32/7.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.32/7.71  tff('#skF_5', type, '#skF_5': $i).
% 14.32/7.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.32/7.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 14.32/7.71  tff('#skF_6', type, '#skF_6': $i).
% 14.32/7.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.32/7.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.32/7.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.32/7.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.32/7.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.32/7.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.32/7.71  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 14.32/7.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.32/7.71  tff('#skF_4', type, '#skF_4': $i).
% 14.32/7.71  tff('#skF_3', type, '#skF_3': $i > $i).
% 14.32/7.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.32/7.71  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 14.32/7.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.32/7.71  
% 14.32/7.73  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 14.32/7.73  tff(f_104, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 14.32/7.73  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 14.32/7.73  tff(f_77, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 14.32/7.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.32/7.73  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.32/7.73  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 14.32/7.73  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 14.32/7.73  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 14.32/7.73  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.32/7.73  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.32/7.73  tff(f_83, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 14.32/7.73  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 14.32/7.73  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.32/7.73  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.32/7.73  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.32/7.73  tff(c_62, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.32/7.73  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.32/7.73  tff(c_40, plain, (![A_40]: (r2_hidden('#skF_3'(A_40), A_40) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.32/7.73  tff(c_196, plain, (![C_104, A_105, B_106]: (r2_hidden(C_104, A_105) | ~r2_hidden(C_104, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.32/7.73  tff(c_200, plain, (![A_107, A_108]: (r2_hidden('#skF_3'(A_107), A_108) | ~m1_subset_1(A_107, k1_zfmisc_1(A_108)) | k1_xboole_0=A_107)), inference(resolution, [status(thm)], [c_40, c_196])).
% 14.32/7.73  tff(c_30, plain, (![A_34, C_36, B_35]: (r2_hidden(k2_mcart_1(A_34), C_36) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.32/7.73  tff(c_431, plain, (![A_131, C_132, B_133]: (r2_hidden(k2_mcart_1('#skF_3'(A_131)), C_132) | ~m1_subset_1(A_131, k1_zfmisc_1(k2_zfmisc_1(B_133, C_132))) | k1_xboole_0=A_131)), inference(resolution, [status(thm)], [c_200, c_30])).
% 14.32/7.73  tff(c_442, plain, (r2_hidden(k2_mcart_1('#skF_3'('#skF_6')), '#skF_5') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_431])).
% 14.32/7.73  tff(c_445, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_442])).
% 14.32/7.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.32/7.73  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.32/7.73  tff(c_127, plain, (![A_82, B_83]: (r2_hidden(A_82, B_83) | k4_xboole_0(k1_tarski(A_82), B_83)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.32/7.73  tff(c_143, plain, (![A_85]: (r2_hidden(A_85, k1_xboole_0) | k1_tarski(A_85)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_127])).
% 14.32/7.73  tff(c_22, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.32/7.73  tff(c_149, plain, (![A_85]: (~r1_tarski(k1_xboole_0, A_85) | k1_tarski(A_85)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_22])).
% 14.32/7.73  tff(c_153, plain, (![A_85]: (k1_tarski(A_85)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_149])).
% 14.32/7.73  tff(c_460, plain, (![A_85]: (k1_tarski(A_85)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_153])).
% 14.32/7.73  tff(c_483, plain, (![A_139, B_140, C_141]: (r2_hidden('#skF_1'(A_139, B_140, C_141), B_140) | k1_relset_1(B_140, A_139, C_141)=B_140 | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(B_140, A_139))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.32/7.73  tff(c_486, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_4'), '#skF_6'), k1_tarski('#skF_4')) | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_60, c_483])).
% 14.32/7.73  tff(c_607, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_486])).
% 14.32/7.73  tff(c_465, plain, (![A_40]: (r2_hidden('#skF_3'(A_40), A_40) | A_40='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_40])).
% 14.32/7.73  tff(c_18, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.32/7.73  tff(c_467, plain, (![A_15]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_18])).
% 14.32/7.73  tff(c_833, plain, (![D_189, A_190, B_191, C_192]: (r2_hidden(k4_tarski(D_189, '#skF_2'(A_190, B_191, C_192, D_189)), C_192) | ~r2_hidden(D_189, B_191) | k1_relset_1(B_191, A_190, C_192)!=B_191 | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(B_191, A_190))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.32/7.73  tff(c_110, plain, (![A_80, B_81]: (k4_xboole_0(k1_tarski(A_80), B_81)=k1_xboole_0 | ~r2_hidden(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.32/7.73  tff(c_117, plain, (![A_80]: (k1_tarski(A_80)=k1_xboole_0 | ~r2_hidden(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_4])).
% 14.32/7.73  tff(c_163, plain, (![A_80]: (~r2_hidden(A_80, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_153, c_117])).
% 14.32/7.73  tff(c_459, plain, (![A_80]: (~r2_hidden(A_80, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_163])).
% 14.32/7.73  tff(c_846, plain, (![D_189, B_191, A_190]: (~r2_hidden(D_189, B_191) | k1_relset_1(B_191, A_190, '#skF_6')!=B_191 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_191, A_190))))), inference(resolution, [status(thm)], [c_833, c_459])).
% 14.32/7.73  tff(c_873, plain, (![D_193, B_194, A_195]: (~r2_hidden(D_193, B_194) | k1_relset_1(B_194, A_195, '#skF_6')!=B_194)), inference(demodulation, [status(thm), theory('equality')], [c_467, c_846])).
% 14.32/7.73  tff(c_889, plain, (![A_196, A_197]: (k1_relset_1(A_196, A_197, '#skF_6')!=A_196 | A_196='#skF_6')), inference(resolution, [status(thm)], [c_465, c_873])).
% 14.32/7.73  tff(c_895, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_607, c_889])).
% 14.32/7.73  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_460, c_895])).
% 14.32/7.73  tff(c_903, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_486])).
% 14.32/7.73  tff(c_469, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_58])).
% 14.32/7.73  tff(c_52, plain, (![B_63, A_62, C_64]: (k1_xboole_0=B_63 | k1_relset_1(A_62, B_63, C_64)=A_62 | ~v1_funct_2(C_64, A_62, B_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.32/7.73  tff(c_559, plain, (![B_147, A_148, C_149]: (B_147='#skF_6' | k1_relset_1(A_148, B_147, C_149)=A_148 | ~v1_funct_2(C_149, A_148, B_147) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_52])).
% 14.32/7.73  tff(c_1175, plain, (![B_238, A_239]: (B_238='#skF_6' | k1_relset_1(A_239, B_238, '#skF_6')=A_239 | ~v1_funct_2('#skF_6', A_239, B_238))), inference(resolution, [status(thm)], [c_467, c_559])).
% 14.32/7.73  tff(c_1187, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1175])).
% 14.32/7.73  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_469, c_1187])).
% 14.32/7.73  tff(c_1198, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_442])).
% 14.32/7.73  tff(c_36, plain, (![A_37, B_38, C_39]: (k1_mcart_1(A_37)=B_38 | ~r2_hidden(A_37, k2_zfmisc_1(k1_tarski(B_38), C_39)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.32/7.73  tff(c_1285, plain, (![A_255, B_256, C_257]: (k1_mcart_1('#skF_3'(A_255))=B_256 | ~m1_subset_1(A_255, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_256), C_257))) | k1_xboole_0=A_255)), inference(resolution, [status(thm)], [c_200, c_36])).
% 14.32/7.73  tff(c_1291, plain, (k1_mcart_1('#skF_3'('#skF_6'))='#skF_4' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_1285])).
% 14.32/7.73  tff(c_1298, plain, (k1_mcart_1('#skF_3'('#skF_6'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1198, c_1291])).
% 14.32/7.73  tff(c_32, plain, (![A_34, B_35, C_36]: (r2_hidden(k1_mcart_1(A_34), B_35) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.32/7.73  tff(c_1305, plain, (![A_258, B_259, C_260]: (r2_hidden(k1_mcart_1('#skF_3'(A_258)), B_259) | ~m1_subset_1(A_258, k1_zfmisc_1(k2_zfmisc_1(B_259, C_260))) | k1_xboole_0=A_258)), inference(resolution, [status(thm)], [c_200, c_32])).
% 14.32/7.73  tff(c_1311, plain, (r2_hidden(k1_mcart_1('#skF_3'('#skF_6')), k1_tarski('#skF_4')) | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_1305])).
% 14.32/7.73  tff(c_1317, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_1311])).
% 14.32/7.73  tff(c_1318, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1198, c_1317])).
% 14.32/7.73  tff(c_1827, plain, (![D_326, C_327, B_328, A_329]: (r2_hidden(k1_funct_1(D_326, C_327), B_328) | k1_xboole_0=B_328 | ~r2_hidden(C_327, A_329) | ~m1_subset_1(D_326, k1_zfmisc_1(k2_zfmisc_1(A_329, B_328))) | ~v1_funct_2(D_326, A_329, B_328) | ~v1_funct_1(D_326))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.32/7.73  tff(c_34210, plain, (![D_1857, B_1858]: (r2_hidden(k1_funct_1(D_1857, '#skF_4'), B_1858) | k1_xboole_0=B_1858 | ~m1_subset_1(D_1857, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), B_1858))) | ~v1_funct_2(D_1857, k1_tarski('#skF_4'), B_1858) | ~v1_funct_1(D_1857))), inference(resolution, [status(thm)], [c_1318, c_1827])).
% 14.32/7.73  tff(c_34257, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_34210])).
% 14.32/7.73  tff(c_34267, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_34257])).
% 14.32/7.73  tff(c_34269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_34267])).
% 14.32/7.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.32/7.73  
% 14.32/7.73  Inference rules
% 14.32/7.73  ----------------------
% 14.32/7.73  #Ref     : 0
% 14.32/7.73  #Sup     : 8955
% 14.32/7.73  #Fact    : 14
% 14.32/7.73  #Define  : 0
% 14.32/7.73  #Split   : 20
% 14.32/7.73  #Chain   : 0
% 14.32/7.73  #Close   : 0
% 14.32/7.73  
% 14.32/7.73  Ordering : KBO
% 14.32/7.73  
% 14.32/7.73  Simplification rules
% 14.32/7.73  ----------------------
% 14.32/7.73  #Subsume      : 3531
% 14.32/7.73  #Demod        : 3577
% 14.32/7.73  #Tautology    : 1511
% 14.32/7.73  #SimpNegUnit  : 179
% 14.32/7.73  #BackRed      : 45
% 14.32/7.73  
% 14.32/7.73  #Partial instantiations: 0
% 14.32/7.73  #Strategies tried      : 1
% 14.32/7.73  
% 14.32/7.73  Timing (in seconds)
% 14.32/7.73  ----------------------
% 14.32/7.73  Preprocessing        : 0.34
% 14.32/7.73  Parsing              : 0.18
% 14.32/7.73  CNF conversion       : 0.03
% 14.32/7.73  Main loop            : 6.62
% 14.32/7.73  Inferencing          : 1.38
% 14.32/7.73  Reduction            : 1.72
% 14.32/7.73  Demodulation         : 1.07
% 14.32/7.73  BG Simplification    : 0.15
% 14.32/7.73  Subsumption          : 3.03
% 14.32/7.73  Abstraction          : 0.25
% 14.32/7.73  MUC search           : 0.00
% 14.32/7.73  Cooper               : 0.00
% 14.32/7.73  Total                : 7.00
% 14.32/7.73  Index Insertion      : 0.00
% 14.32/7.73  Index Deletion       : 0.00
% 14.32/7.73  Index Matching       : 0.00
% 14.32/7.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
