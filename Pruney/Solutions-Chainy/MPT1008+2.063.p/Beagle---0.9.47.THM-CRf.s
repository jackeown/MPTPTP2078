%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:34 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 260 expanded)
%              Number of leaves         :   42 ( 105 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 571 expanded)
%              Number of equality atoms :  101 ( 274 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_135,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_139,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_135])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_139,c_38])).

tff(c_148,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_259,plain,(
    ! [B_110,A_111] :
      ( k1_tarski(k1_funct_1(B_110,A_111)) = k2_relat_1(B_110)
      | k1_tarski(A_111) != k1_relat_1(B_110)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_249,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_253,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_249])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_254,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_60])).

tff(c_265,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_254])).

tff(c_293,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_68,c_265])).

tff(c_185,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_189,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_185])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_391,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k1_enumset1(A_144,B_145,C_146) = D_147
      | k2_tarski(A_144,C_146) = D_147
      | k2_tarski(B_145,C_146) = D_147
      | k2_tarski(A_144,B_145) = D_147
      | k1_tarski(C_146) = D_147
      | k1_tarski(B_145) = D_147
      | k1_tarski(A_144) = D_147
      | k1_xboole_0 = D_147
      | ~ r1_tarski(D_147,k1_enumset1(A_144,B_145,C_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_422,plain,(
    ! [A_3,B_4,D_147] :
      ( k1_enumset1(A_3,A_3,B_4) = D_147
      | k2_tarski(A_3,B_4) = D_147
      | k2_tarski(A_3,B_4) = D_147
      | k2_tarski(A_3,A_3) = D_147
      | k1_tarski(B_4) = D_147
      | k1_tarski(A_3) = D_147
      | k1_tarski(A_3) = D_147
      | k1_xboole_0 = D_147
      | ~ r1_tarski(D_147,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_391])).

tff(c_467,plain,(
    ! [A_157,B_158,D_159] :
      ( k2_tarski(A_157,B_158) = D_159
      | k2_tarski(A_157,B_158) = D_159
      | k2_tarski(A_157,B_158) = D_159
      | k1_tarski(A_157) = D_159
      | k1_tarski(B_158) = D_159
      | k1_tarski(A_157) = D_159
      | k1_tarski(A_157) = D_159
      | k1_xboole_0 = D_159
      | ~ r1_tarski(D_159,k2_tarski(A_157,B_158)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_422])).

tff(c_506,plain,(
    ! [A_160,B_161,B_162] :
      ( k2_tarski(A_160,B_161) = k1_relat_1(B_162)
      | k1_tarski(B_161) = k1_relat_1(B_162)
      | k1_tarski(A_160) = k1_relat_1(B_162)
      | k1_relat_1(B_162) = k1_xboole_0
      | ~ v4_relat_1(B_162,k2_tarski(A_160,B_161))
      | ~ v1_relat_1(B_162) ) ),
    inference(resolution,[status(thm)],[c_30,c_467])).

tff(c_509,plain,(
    ! [A_2,B_162] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_162)
      | k1_tarski(A_2) = k1_relat_1(B_162)
      | k1_tarski(A_2) = k1_relat_1(B_162)
      | k1_relat_1(B_162) = k1_xboole_0
      | ~ v4_relat_1(B_162,k1_tarski(A_2))
      | ~ v1_relat_1(B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_506])).

tff(c_511,plain,(
    ! [A_163,B_164] :
      ( k1_tarski(A_163) = k1_relat_1(B_164)
      | k1_tarski(A_163) = k1_relat_1(B_164)
      | k1_tarski(A_163) = k1_relat_1(B_164)
      | k1_relat_1(B_164) = k1_xboole_0
      | ~ v4_relat_1(B_164,k1_tarski(A_163))
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_509])).

tff(c_517,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_511])).

tff(c_520,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_517])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_293,c_520])).

tff(c_523,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_531,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_523,c_34])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_530,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_523,c_32])).

tff(c_698,plain,(
    ! [B_212,A_213] :
      ( k1_tarski(k1_funct_1(B_212,A_213)) = k2_relat_1(B_212)
      | k1_tarski(A_213) != k1_relat_1(B_212)
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_673,plain,(
    ! [A_206,B_207,C_208] :
      ( k2_relset_1(A_206,B_207,C_208) = k2_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_676,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_673])).

tff(c_678,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_676])).

tff(c_679,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_60])).

tff(c_704,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_679])).

tff(c_731,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_68,c_531,c_530,c_704])).

tff(c_52,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_528,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | A_28 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_52])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_529,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_2])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_532,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_58,plain,(
    ! [D_41,C_40,A_38,B_39] :
      ( r2_hidden(k1_funct_1(D_41,C_40),k2_relset_1(A_38,B_39,D_41))
      | k1_xboole_0 = B_39
      | ~ r2_hidden(C_40,A_38)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(D_41,A_38,B_39)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_734,plain,(
    ! [D_214,C_215,A_216,B_217] :
      ( r2_hidden(k1_funct_1(D_214,C_215),k2_relset_1(A_216,B_217,D_214))
      | B_217 = '#skF_4'
      | ~ r2_hidden(C_215,A_216)
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_2(D_214,A_216,B_217)
      | ~ v1_funct_1(D_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_58])).

tff(c_744,plain,(
    ! [C_215] :
      ( r2_hidden(k1_funct_1('#skF_4',C_215),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_215,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_734])).

tff(c_749,plain,(
    ! [C_215] :
      ( r2_hidden(k1_funct_1('#skF_4',C_215),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_215,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_744])).

tff(c_751,plain,(
    ! [C_218] :
      ( r2_hidden(k1_funct_1('#skF_4',C_218),'#skF_4')
      | ~ r2_hidden(C_218,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_749])).

tff(c_42,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_758,plain,(
    ! [C_218] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_218))
      | ~ r2_hidden(C_218,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_751,c_42])).

tff(c_766,plain,(
    ! [C_219] : ~ r2_hidden(C_219,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_758])).

tff(c_770,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_528,c_766])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.26/1.52  
% 3.26/1.52  %Foreground sorts:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Background operators:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Foreground operators:
% 3.26/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.26/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.26/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.26/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.26/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.52  
% 3.26/1.54  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.26/1.54  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.26/1.54  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.26/1.54  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.26/1.54  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.26/1.54  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.54  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.54  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.26/1.54  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.54  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.26/1.54  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.26/1.54  tff(f_120, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.26/1.54  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.54  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.26/1.54  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.26/1.54  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.54  tff(c_135, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.54  tff(c_139, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_135])).
% 3.26/1.54  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.54  tff(c_38, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.54  tff(c_146, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_139, c_38])).
% 3.26/1.54  tff(c_148, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 3.26/1.54  tff(c_259, plain, (![B_110, A_111]: (k1_tarski(k1_funct_1(B_110, A_111))=k2_relat_1(B_110) | k1_tarski(A_111)!=k1_relat_1(B_110) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.54  tff(c_249, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.26/1.54  tff(c_253, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_249])).
% 3.26/1.54  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.54  tff(c_254, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_60])).
% 3.26/1.54  tff(c_265, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_259, c_254])).
% 3.26/1.54  tff(c_293, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_68, c_265])).
% 3.26/1.54  tff(c_185, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.26/1.54  tff(c_189, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_185])).
% 3.26/1.54  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.54  tff(c_30, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.54  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.54  tff(c_391, plain, (![A_144, B_145, C_146, D_147]: (k1_enumset1(A_144, B_145, C_146)=D_147 | k2_tarski(A_144, C_146)=D_147 | k2_tarski(B_145, C_146)=D_147 | k2_tarski(A_144, B_145)=D_147 | k1_tarski(C_146)=D_147 | k1_tarski(B_145)=D_147 | k1_tarski(A_144)=D_147 | k1_xboole_0=D_147 | ~r1_tarski(D_147, k1_enumset1(A_144, B_145, C_146)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.26/1.54  tff(c_422, plain, (![A_3, B_4, D_147]: (k1_enumset1(A_3, A_3, B_4)=D_147 | k2_tarski(A_3, B_4)=D_147 | k2_tarski(A_3, B_4)=D_147 | k2_tarski(A_3, A_3)=D_147 | k1_tarski(B_4)=D_147 | k1_tarski(A_3)=D_147 | k1_tarski(A_3)=D_147 | k1_xboole_0=D_147 | ~r1_tarski(D_147, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_391])).
% 3.26/1.54  tff(c_467, plain, (![A_157, B_158, D_159]: (k2_tarski(A_157, B_158)=D_159 | k2_tarski(A_157, B_158)=D_159 | k2_tarski(A_157, B_158)=D_159 | k1_tarski(A_157)=D_159 | k1_tarski(B_158)=D_159 | k1_tarski(A_157)=D_159 | k1_tarski(A_157)=D_159 | k1_xboole_0=D_159 | ~r1_tarski(D_159, k2_tarski(A_157, B_158)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_422])).
% 3.26/1.54  tff(c_506, plain, (![A_160, B_161, B_162]: (k2_tarski(A_160, B_161)=k1_relat_1(B_162) | k1_tarski(B_161)=k1_relat_1(B_162) | k1_tarski(A_160)=k1_relat_1(B_162) | k1_relat_1(B_162)=k1_xboole_0 | ~v4_relat_1(B_162, k2_tarski(A_160, B_161)) | ~v1_relat_1(B_162))), inference(resolution, [status(thm)], [c_30, c_467])).
% 3.26/1.54  tff(c_509, plain, (![A_2, B_162]: (k2_tarski(A_2, A_2)=k1_relat_1(B_162) | k1_tarski(A_2)=k1_relat_1(B_162) | k1_tarski(A_2)=k1_relat_1(B_162) | k1_relat_1(B_162)=k1_xboole_0 | ~v4_relat_1(B_162, k1_tarski(A_2)) | ~v1_relat_1(B_162))), inference(superposition, [status(thm), theory('equality')], [c_4, c_506])).
% 3.26/1.54  tff(c_511, plain, (![A_163, B_164]: (k1_tarski(A_163)=k1_relat_1(B_164) | k1_tarski(A_163)=k1_relat_1(B_164) | k1_tarski(A_163)=k1_relat_1(B_164) | k1_relat_1(B_164)=k1_xboole_0 | ~v4_relat_1(B_164, k1_tarski(A_163)) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_509])).
% 3.26/1.54  tff(c_517, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_189, c_511])).
% 3.26/1.54  tff(c_520, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_517])).
% 3.26/1.54  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_293, c_520])).
% 3.26/1.54  tff(c_523, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 3.26/1.54  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.54  tff(c_531, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_523, c_523, c_34])).
% 3.26/1.54  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.54  tff(c_530, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_523, c_523, c_32])).
% 3.26/1.54  tff(c_698, plain, (![B_212, A_213]: (k1_tarski(k1_funct_1(B_212, A_213))=k2_relat_1(B_212) | k1_tarski(A_213)!=k1_relat_1(B_212) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.54  tff(c_673, plain, (![A_206, B_207, C_208]: (k2_relset_1(A_206, B_207, C_208)=k2_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.26/1.54  tff(c_676, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_673])).
% 3.26/1.54  tff(c_678, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_530, c_676])).
% 3.26/1.54  tff(c_679, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_678, c_60])).
% 3.26/1.54  tff(c_704, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_698, c_679])).
% 3.26/1.54  tff(c_731, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_68, c_531, c_530, c_704])).
% 3.26/1.54  tff(c_52, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.26/1.54  tff(c_528, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | A_28='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_52])).
% 3.26/1.54  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.54  tff(c_529, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_2])).
% 3.26/1.54  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.54  tff(c_532, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_523, c_62])).
% 3.26/1.54  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.54  tff(c_58, plain, (![D_41, C_40, A_38, B_39]: (r2_hidden(k1_funct_1(D_41, C_40), k2_relset_1(A_38, B_39, D_41)) | k1_xboole_0=B_39 | ~r2_hidden(C_40, A_38) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(D_41, A_38, B_39) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.26/1.54  tff(c_734, plain, (![D_214, C_215, A_216, B_217]: (r2_hidden(k1_funct_1(D_214, C_215), k2_relset_1(A_216, B_217, D_214)) | B_217='#skF_4' | ~r2_hidden(C_215, A_216) | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_2(D_214, A_216, B_217) | ~v1_funct_1(D_214))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_58])).
% 3.26/1.54  tff(c_744, plain, (![C_215]: (r2_hidden(k1_funct_1('#skF_4', C_215), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_215, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_678, c_734])).
% 3.26/1.54  tff(c_749, plain, (![C_215]: (r2_hidden(k1_funct_1('#skF_4', C_215), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_215, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_744])).
% 3.26/1.54  tff(c_751, plain, (![C_218]: (r2_hidden(k1_funct_1('#skF_4', C_218), '#skF_4') | ~r2_hidden(C_218, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_532, c_749])).
% 3.26/1.54  tff(c_42, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.54  tff(c_758, plain, (![C_218]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_218)) | ~r2_hidden(C_218, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_751, c_42])).
% 3.26/1.54  tff(c_766, plain, (![C_219]: (~r2_hidden(C_219, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_758])).
% 3.26/1.54  tff(c_770, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_528, c_766])).
% 3.26/1.54  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_731, c_770])).
% 3.26/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.54  
% 3.26/1.54  Inference rules
% 3.26/1.54  ----------------------
% 3.26/1.54  #Ref     : 0
% 3.26/1.54  #Sup     : 153
% 3.26/1.54  #Fact    : 0
% 3.26/1.54  #Define  : 0
% 3.26/1.54  #Split   : 3
% 3.26/1.54  #Chain   : 0
% 3.26/1.54  #Close   : 0
% 3.26/1.54  
% 3.26/1.54  Ordering : KBO
% 3.26/1.54  
% 3.26/1.54  Simplification rules
% 3.26/1.54  ----------------------
% 3.26/1.54  #Subsume      : 22
% 3.26/1.54  #Demod        : 103
% 3.26/1.54  #Tautology    : 74
% 3.26/1.54  #SimpNegUnit  : 7
% 3.26/1.54  #BackRed      : 10
% 3.26/1.54  
% 3.26/1.54  #Partial instantiations: 0
% 3.26/1.54  #Strategies tried      : 1
% 3.26/1.54  
% 3.26/1.54  Timing (in seconds)
% 3.26/1.54  ----------------------
% 3.26/1.54  Preprocessing        : 0.35
% 3.26/1.54  Parsing              : 0.19
% 3.26/1.54  CNF conversion       : 0.02
% 3.26/1.54  Main loop            : 0.41
% 3.26/1.54  Inferencing          : 0.15
% 3.26/1.54  Reduction            : 0.13
% 3.26/1.54  Demodulation         : 0.10
% 3.26/1.54  BG Simplification    : 0.02
% 3.26/1.54  Subsumption          : 0.07
% 3.26/1.54  Abstraction          : 0.02
% 3.26/1.54  MUC search           : 0.00
% 3.26/1.54  Cooper               : 0.00
% 3.26/1.54  Total                : 0.80
% 3.26/1.54  Index Insertion      : 0.00
% 3.26/1.55  Index Deletion       : 0.00
% 3.53/1.55  Index Matching       : 0.00
% 3.53/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
