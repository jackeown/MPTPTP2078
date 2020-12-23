%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 313 expanded)
%              Number of leaves         :   47 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 725 expanded)
%              Number of equality atoms :   51 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

tff(c_54,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_107,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_56,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_88,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_92,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_130,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_134,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_130])).

tff(c_210,plain,(
    ! [B_127,A_128,C_129] :
      ( k1_xboole_0 = B_127
      | k1_relset_1(A_128,B_127,C_129) = A_128
      | ~ v1_funct_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_213,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_210])).

tff(c_216,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_134,c_213])).

tff(c_217,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_190,plain,(
    ! [B_119,C_120,A_121] :
      ( r2_hidden(k1_funct_1(B_119,C_120),A_121)
      | ~ r2_hidden(C_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v5_relat_1(B_119,A_121)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    ! [B_119,C_120,A_1] :
      ( k1_funct_1(B_119,C_120) = A_1
      | ~ r2_hidden(C_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v5_relat_1(B_119,k1_tarski(A_1))
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_221,plain,(
    ! [C_120,A_1] :
      ( k1_funct_1('#skF_6',C_120) = A_1
      | ~ r2_hidden(C_120,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_1))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_195])).

tff(c_231,plain,(
    ! [C_130,A_131] :
      ( k1_funct_1('#skF_6',C_130) = A_131
      | ~ r2_hidden(C_130,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_62,c_221])).

tff(c_247,plain,(
    ! [A_132] :
      ( k1_funct_1('#skF_6','#skF_5') = A_132
      | ~ v5_relat_1('#skF_6',k1_tarski(A_132)) ) ),
    inference(resolution,[status(thm)],[c_56,c_231])).

tff(c_250,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_247])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_250])).

tff(c_255,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_260,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_60])).

tff(c_259,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_58])).

tff(c_44,plain,(
    ! [C_57,A_55] :
      ( k1_xboole_0 = C_57
      | ~ v1_funct_2(C_57,A_55,k1_xboole_0)
      | k1_xboole_0 = A_55
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_324,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_259,c_44])).

tff(c_344,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_324])).

tff(c_353,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_366,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_2])).

tff(c_360,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_255])).

tff(c_16,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k4_enumset1(A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,F_26) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_283,plain,(
    ! [B_137,A_139,G_138,C_134,E_136,D_135,F_133] : k6_enumset1(A_139,A_139,B_137,C_134,D_135,E_136,F_133,G_138) = k5_enumset1(A_139,B_137,C_134,D_135,E_136,F_133,G_138) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [H_41,D_37,A_34,F_39,B_35,G_40,C_36,E_38] : ~ v1_xboole_0(k6_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,G_40,H_41)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_457,plain,(
    ! [E_149,D_150,G_148,F_145,B_151,A_147,C_146] : ~ v1_xboole_0(k5_enumset1(A_147,B_151,C_146,D_150,E_149,F_145,G_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_30])).

tff(c_461,plain,(
    ! [A_152,C_154,B_156,F_155,D_153,E_157] : ~ v1_xboole_0(k4_enumset1(A_152,B_156,C_154,D_153,E_157,F_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_457])).

tff(c_464,plain,(
    ! [C_162,D_161,A_160,E_159,B_158] : ~ v1_xboole_0(k3_enumset1(A_160,B_158,C_162,D_161,E_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_461])).

tff(c_501,plain,(
    ! [A_164,B_165,C_166,D_167] : ~ v1_xboole_0(k2_enumset1(A_164,B_165,C_166,D_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_464])).

tff(c_504,plain,(
    ! [A_168,B_169,C_170] : ~ v1_xboole_0(k1_enumset1(A_168,B_169,C_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_501])).

tff(c_507,plain,(
    ! [A_171,B_172] : ~ v1_xboole_0(k2_tarski(A_171,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_504])).

tff(c_510,plain,(
    ! [A_173] : ~ v1_xboole_0(k1_tarski(A_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_507])).

tff(c_514,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_510])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_514])).

tff(c_520,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_534,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_2])).

tff(c_528,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_255])).

tff(c_586,plain,(
    ! [F_178,D_183,G_181,A_180,B_184,E_182,C_179] : ~ v1_xboole_0(k5_enumset1(A_180,B_184,C_179,D_183,E_182,F_178,G_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_30])).

tff(c_618,plain,(
    ! [C_187,A_185,B_189,F_188,E_190,D_186] : ~ v1_xboole_0(k4_enumset1(A_185,B_189,C_187,D_186,E_190,F_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_586])).

tff(c_655,plain,(
    ! [C_196,B_192,A_194,E_193,D_195] : ~ v1_xboole_0(k3_enumset1(A_194,B_192,C_196,D_195,E_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_618])).

tff(c_658,plain,(
    ! [A_197,B_198,C_199,D_200] : ~ v1_xboole_0(k2_enumset1(A_197,B_198,C_199,D_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_655])).

tff(c_661,plain,(
    ! [A_201,B_202,C_203] : ~ v1_xboole_0(k1_enumset1(A_201,B_202,C_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_658])).

tff(c_664,plain,(
    ! [A_204,B_205] : ~ v1_xboole_0(k2_tarski(A_204,B_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_661])).

tff(c_667,plain,(
    ! [A_206] : ~ v1_xboole_0(k1_tarski(A_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_664])).

tff(c_671,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_667])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:25:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.89/1.40  
% 2.89/1.40  %Foreground sorts:
% 2.89/1.40  
% 2.89/1.40  
% 2.89/1.40  %Background operators:
% 2.89/1.40  
% 2.89/1.40  
% 2.89/1.40  %Foreground operators:
% 2.89/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.89/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.40  
% 2.89/1.41  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.89/1.41  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.89/1.41  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.89/1.41  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.89/1.41  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.89/1.41  tff(f_61, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.89/1.41  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.89/1.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.89/1.41  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.89/1.41  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.89/1.41  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.89/1.41  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.89/1.41  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.89/1.41  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.89/1.41  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.89/1.41  tff(f_50, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_subset_1)).
% 2.89/1.41  tff(c_54, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.41  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.41  tff(c_107, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.89/1.41  tff(c_111, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_107])).
% 2.89/1.41  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.41  tff(c_88, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.41  tff(c_92, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_88])).
% 2.89/1.41  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.41  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.41  tff(c_130, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.41  tff(c_134, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_130])).
% 2.89/1.41  tff(c_210, plain, (![B_127, A_128, C_129]: (k1_xboole_0=B_127 | k1_relset_1(A_128, B_127, C_129)=A_128 | ~v1_funct_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.41  tff(c_213, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_210])).
% 2.89/1.41  tff(c_216, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_134, c_213])).
% 2.89/1.41  tff(c_217, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_216])).
% 2.89/1.41  tff(c_190, plain, (![B_119, C_120, A_121]: (r2_hidden(k1_funct_1(B_119, C_120), A_121) | ~r2_hidden(C_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v5_relat_1(B_119, A_121) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.41  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.41  tff(c_195, plain, (![B_119, C_120, A_1]: (k1_funct_1(B_119, C_120)=A_1 | ~r2_hidden(C_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v5_relat_1(B_119, k1_tarski(A_1)) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_190, c_4])).
% 2.89/1.41  tff(c_221, plain, (![C_120, A_1]: (k1_funct_1('#skF_6', C_120)=A_1 | ~r2_hidden(C_120, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_tarski(A_1)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_195])).
% 2.89/1.41  tff(c_231, plain, (![C_130, A_131]: (k1_funct_1('#skF_6', C_130)=A_131 | ~r2_hidden(C_130, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_131)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_62, c_221])).
% 2.89/1.41  tff(c_247, plain, (![A_132]: (k1_funct_1('#skF_6', '#skF_5')=A_132 | ~v5_relat_1('#skF_6', k1_tarski(A_132)))), inference(resolution, [status(thm)], [c_56, c_231])).
% 2.89/1.41  tff(c_250, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_111, c_247])).
% 2.89/1.41  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_250])).
% 2.89/1.41  tff(c_255, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_216])).
% 2.89/1.41  tff(c_260, plain, (v1_funct_2('#skF_6', '#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_60])).
% 2.89/1.41  tff(c_259, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_58])).
% 2.89/1.41  tff(c_44, plain, (![C_57, A_55]: (k1_xboole_0=C_57 | ~v1_funct_2(C_57, A_55, k1_xboole_0) | k1_xboole_0=A_55 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.41  tff(c_324, plain, (k1_xboole_0='#skF_6' | ~v1_funct_2('#skF_6', '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_259, c_44])).
% 2.89/1.41  tff(c_344, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_324])).
% 2.89/1.41  tff(c_353, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_344])).
% 2.89/1.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.89/1.41  tff(c_366, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_2])).
% 2.89/1.41  tff(c_360, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_255])).
% 2.89/1.41  tff(c_16, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.41  tff(c_18, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.41  tff(c_20, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.41  tff(c_22, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.41  tff(c_24, plain, (![C_18, B_17, A_16, D_19, E_20]: (k4_enumset1(A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.41  tff(c_26, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, F_26)=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.41  tff(c_283, plain, (![B_137, A_139, G_138, C_134, E_136, D_135, F_133]: (k6_enumset1(A_139, A_139, B_137, C_134, D_135, E_136, F_133, G_138)=k5_enumset1(A_139, B_137, C_134, D_135, E_136, F_133, G_138))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.41  tff(c_30, plain, (![H_41, D_37, A_34, F_39, B_35, G_40, C_36, E_38]: (~v1_xboole_0(k6_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, G_40, H_41)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.41  tff(c_457, plain, (![E_149, D_150, G_148, F_145, B_151, A_147, C_146]: (~v1_xboole_0(k5_enumset1(A_147, B_151, C_146, D_150, E_149, F_145, G_148)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_30])).
% 2.89/1.41  tff(c_461, plain, (![A_152, C_154, B_156, F_155, D_153, E_157]: (~v1_xboole_0(k4_enumset1(A_152, B_156, C_154, D_153, E_157, F_155)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_457])).
% 2.89/1.41  tff(c_464, plain, (![C_162, D_161, A_160, E_159, B_158]: (~v1_xboole_0(k3_enumset1(A_160, B_158, C_162, D_161, E_159)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_461])).
% 2.89/1.41  tff(c_501, plain, (![A_164, B_165, C_166, D_167]: (~v1_xboole_0(k2_enumset1(A_164, B_165, C_166, D_167)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_464])).
% 2.89/1.41  tff(c_504, plain, (![A_168, B_169, C_170]: (~v1_xboole_0(k1_enumset1(A_168, B_169, C_170)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_501])).
% 2.89/1.41  tff(c_507, plain, (![A_171, B_172]: (~v1_xboole_0(k2_tarski(A_171, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_504])).
% 2.89/1.41  tff(c_510, plain, (![A_173]: (~v1_xboole_0(k1_tarski(A_173)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_507])).
% 2.89/1.41  tff(c_514, plain, (~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_360, c_510])).
% 2.89/1.41  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_514])).
% 2.89/1.41  tff(c_520, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_344])).
% 2.89/1.41  tff(c_534, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_2])).
% 2.89/1.41  tff(c_528, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_520, c_255])).
% 2.89/1.41  tff(c_586, plain, (![F_178, D_183, G_181, A_180, B_184, E_182, C_179]: (~v1_xboole_0(k5_enumset1(A_180, B_184, C_179, D_183, E_182, F_178, G_181)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_30])).
% 2.89/1.41  tff(c_618, plain, (![C_187, A_185, B_189, F_188, E_190, D_186]: (~v1_xboole_0(k4_enumset1(A_185, B_189, C_187, D_186, E_190, F_188)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_586])).
% 2.89/1.41  tff(c_655, plain, (![C_196, B_192, A_194, E_193, D_195]: (~v1_xboole_0(k3_enumset1(A_194, B_192, C_196, D_195, E_193)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_618])).
% 2.89/1.41  tff(c_658, plain, (![A_197, B_198, C_199, D_200]: (~v1_xboole_0(k2_enumset1(A_197, B_198, C_199, D_200)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_655])).
% 2.89/1.41  tff(c_661, plain, (![A_201, B_202, C_203]: (~v1_xboole_0(k1_enumset1(A_201, B_202, C_203)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_658])).
% 2.89/1.41  tff(c_664, plain, (![A_204, B_205]: (~v1_xboole_0(k2_tarski(A_204, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_661])).
% 2.89/1.41  tff(c_667, plain, (![A_206]: (~v1_xboole_0(k1_tarski(A_206)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_664])).
% 2.89/1.41  tff(c_671, plain, (~v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_528, c_667])).
% 2.89/1.41  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_671])).
% 2.89/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.41  
% 2.89/1.41  Inference rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Ref     : 0
% 2.89/1.41  #Sup     : 140
% 2.89/1.41  #Fact    : 0
% 2.89/1.41  #Define  : 0
% 2.89/1.41  #Split   : 2
% 2.89/1.41  #Chain   : 0
% 2.89/1.41  #Close   : 0
% 2.89/1.41  
% 2.89/1.41  Ordering : KBO
% 2.89/1.41  
% 2.89/1.41  Simplification rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Subsume      : 3
% 2.89/1.41  #Demod        : 123
% 2.89/1.41  #Tautology    : 72
% 2.89/1.41  #SimpNegUnit  : 2
% 2.89/1.41  #BackRed      : 33
% 2.89/1.41  
% 2.89/1.41  #Partial instantiations: 0
% 2.89/1.41  #Strategies tried      : 1
% 2.89/1.41  
% 2.89/1.41  Timing (in seconds)
% 2.89/1.41  ----------------------
% 2.89/1.42  Preprocessing        : 0.33
% 2.89/1.42  Parsing              : 0.18
% 2.89/1.42  CNF conversion       : 0.02
% 2.89/1.42  Main loop            : 0.32
% 2.89/1.42  Inferencing          : 0.11
% 2.89/1.42  Reduction            : 0.10
% 2.89/1.42  Demodulation         : 0.07
% 2.89/1.42  BG Simplification    : 0.02
% 2.89/1.42  Subsumption          : 0.06
% 2.89/1.42  Abstraction          : 0.02
% 2.89/1.42  MUC search           : 0.00
% 2.89/1.42  Cooper               : 0.00
% 2.89/1.42  Total                : 0.69
% 2.89/1.42  Index Insertion      : 0.00
% 2.89/1.42  Index Deletion       : 0.00
% 2.89/1.42  Index Matching       : 0.00
% 2.89/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
