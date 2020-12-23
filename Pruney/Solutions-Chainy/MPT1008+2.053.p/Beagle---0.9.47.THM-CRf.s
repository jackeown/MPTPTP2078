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
% DateTime   : Thu Dec  3 10:14:33 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 385 expanded)
%              Number of leaves         :   44 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  183 ( 808 expanded)
%              Number of equality atoms :   73 ( 353 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_148,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_148])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_166,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156,c_38])).

tff(c_173,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_448,plain,(
    ! [B_109,A_110] :
      ( k1_tarski(k1_funct_1(B_109,A_110)) = k2_relat_1(B_109)
      | k1_tarski(A_110) != k1_relat_1(B_109)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_425,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_433,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_425])).

tff(c_62,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_443,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_62])).

tff(c_454,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_443])).

tff(c_464,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_70,c_454])).

tff(c_207,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_215,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_207])).

tff(c_235,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v4_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(B_14) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_709,plain,(
    ! [B_139,B_140] :
      ( k1_tarski(B_139) = k1_relat_1(B_140)
      | k1_relat_1(B_140) = k1_xboole_0
      | ~ v4_relat_1(B_140,k1_tarski(B_139))
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_235,c_16])).

tff(c_719,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_215,c_709])).

tff(c_727,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_719])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_464,c_727])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_741,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_730,c_32])).

tff(c_36,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_165,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156,c_36])).

tff(c_167,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_732,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_167])).

tff(c_773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_732])).

tff(c_774,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_785,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_774,c_34])).

tff(c_784,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_774,c_32])).

tff(c_1157,plain,(
    ! [B_196,A_197] :
      ( k1_tarski(k1_funct_1(B_196,A_197)) = k2_relat_1(B_196)
      | k1_tarski(A_197) != k1_relat_1(B_196)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_780,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_22])).

tff(c_1053,plain,(
    ! [A_188,B_189,C_190] :
      ( k2_relset_1(A_188,B_189,C_190) = k2_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1057,plain,(
    ! [A_188,B_189] : k2_relset_1(A_188,B_189,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_780,c_1053])).

tff(c_1059,plain,(
    ! [A_188,B_189] : k2_relset_1(A_188,B_189,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_1057])).

tff(c_1060,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_62])).

tff(c_1163,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_1060])).

tff(c_1172,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_70,c_785,c_784,c_1163])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_782,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_8])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_787,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1208,plain,(
    ! [D_204,C_205,A_206,B_207] :
      ( r2_hidden(k1_funct_1(D_204,C_205),k2_relset_1(A_206,B_207,D_204))
      | B_207 = '#skF_4'
      | ~ r2_hidden(C_205,A_206)
      | ~ m1_subset_1(D_204,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2(D_204,A_206,B_207)
      | ~ v1_funct_1(D_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_60])).

tff(c_1216,plain,(
    ! [C_205,B_189,A_188] :
      ( r2_hidden(k1_funct_1('#skF_4',C_205),'#skF_4')
      | B_189 = '#skF_4'
      | ~ r2_hidden(C_205,A_188)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2('#skF_4',A_188,B_189)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_1208])).

tff(c_1624,plain,(
    ! [C_239,B_240,A_241] :
      ( r2_hidden(k1_funct_1('#skF_4',C_239),'#skF_4')
      | B_240 = '#skF_4'
      | ~ r2_hidden(C_239,A_241)
      | ~ v1_funct_2('#skF_4',A_241,B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_780,c_1216])).

tff(c_1994,plain,(
    ! [A_255,B_256,B_257] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_255,B_256)),'#skF_4')
      | B_257 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_255,B_257)
      | r1_tarski(A_255,B_256) ) ),
    inference(resolution,[status(thm)],[c_6,c_1624])).

tff(c_1996,plain,(
    ! [B_256] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'),B_256)),'#skF_4')
      | '#skF_3' = '#skF_4'
      | r1_tarski(k1_tarski('#skF_2'),B_256) ) ),
    inference(resolution,[status(thm)],[c_68,c_1994])).

tff(c_2047,plain,(
    ! [B_261] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'),B_261)),'#skF_4')
      | r1_tarski(k1_tarski('#skF_2'),B_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_1996])).

tff(c_50,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2056,plain,(
    ! [B_261] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'),B_261)))
      | r1_tarski(k1_tarski('#skF_2'),B_261) ) ),
    inference(resolution,[status(thm)],[c_2047,c_50])).

tff(c_2066,plain,(
    ! [B_262] : r1_tarski(k1_tarski('#skF_2'),B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_2056])).

tff(c_891,plain,(
    ! [C_157,A_158,B_159] :
      ( v4_relat_1(C_157,A_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_896,plain,(
    ! [A_158] : v4_relat_1('#skF_4',A_158) ),
    inference(resolution,[status(thm)],[c_780,c_891])).

tff(c_942,plain,(
    ! [B_169,A_170] :
      ( k7_relat_1(B_169,A_170) = B_169
      | ~ v4_relat_1(B_169,A_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_948,plain,(
    ! [A_158] :
      ( k7_relat_1('#skF_4',A_158) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_896,c_942])).

tff(c_952,plain,(
    ! [A_158] : k7_relat_1('#skF_4',A_158) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_948])).

tff(c_1014,plain,(
    ! [B_185,A_186] :
      ( k1_relat_1(k7_relat_1(B_185,A_186)) = A_186
      | ~ r1_tarski(A_186,k1_relat_1(B_185))
      | ~ v1_relat_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1029,plain,(
    ! [A_186] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_186)) = A_186
      | ~ r1_tarski(A_186,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_1014])).

tff(c_1034,plain,(
    ! [A_186] :
      ( A_186 = '#skF_4'
      | ~ r1_tarski(A_186,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_785,c_952,c_1029])).

tff(c_2085,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2066,c_1034])).

tff(c_2109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1172,c_2085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n020.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:45:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.61  
% 3.66/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.66/1.61  
% 3.66/1.61  %Foreground sorts:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Background operators:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Foreground operators:
% 3.66/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.66/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.66/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.61  
% 3.66/1.63  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.66/1.63  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.66/1.63  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.66/1.63  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.66/1.63  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.66/1.63  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.66/1.63  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.66/1.63  tff(f_46, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.66/1.63  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.66/1.63  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.66/1.63  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.66/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.63  tff(f_127, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.66/1.63  tff(f_101, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.66/1.63  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.66/1.63  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.66/1.63  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.63  tff(c_148, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.66/1.63  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_148])).
% 3.66/1.63  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.63  tff(c_38, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.66/1.63  tff(c_166, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_156, c_38])).
% 3.66/1.63  tff(c_173, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_166])).
% 3.66/1.63  tff(c_448, plain, (![B_109, A_110]: (k1_tarski(k1_funct_1(B_109, A_110))=k2_relat_1(B_109) | k1_tarski(A_110)!=k1_relat_1(B_109) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.66/1.63  tff(c_425, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.63  tff(c_433, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_425])).
% 3.66/1.63  tff(c_62, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.63  tff(c_443, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_62])).
% 3.66/1.63  tff(c_454, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_448, c_443])).
% 3.66/1.63  tff(c_464, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_70, c_454])).
% 3.66/1.63  tff(c_207, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.66/1.63  tff(c_215, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_207])).
% 3.66/1.63  tff(c_235, plain, (![B_80, A_81]: (r1_tarski(k1_relat_1(B_80), A_81) | ~v4_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.66/1.63  tff(c_16, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.63  tff(c_709, plain, (![B_139, B_140]: (k1_tarski(B_139)=k1_relat_1(B_140) | k1_relat_1(B_140)=k1_xboole_0 | ~v4_relat_1(B_140, k1_tarski(B_139)) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_235, c_16])).
% 3.66/1.63  tff(c_719, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_215, c_709])).
% 3.66/1.63  tff(c_727, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_719])).
% 3.66/1.63  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_464, c_727])).
% 3.66/1.63  tff(c_730, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_166])).
% 3.66/1.63  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.66/1.63  tff(c_741, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_730, c_730, c_32])).
% 3.66/1.63  tff(c_36, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.66/1.63  tff(c_165, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_156, c_36])).
% 3.66/1.63  tff(c_167, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_165])).
% 3.66/1.63  tff(c_732, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_730, c_167])).
% 3.66/1.63  tff(c_773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_741, c_732])).
% 3.66/1.63  tff(c_774, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_165])).
% 3.66/1.63  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.66/1.63  tff(c_785, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_774, c_34])).
% 3.66/1.63  tff(c_784, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_774, c_32])).
% 3.66/1.63  tff(c_1157, plain, (![B_196, A_197]: (k1_tarski(k1_funct_1(B_196, A_197))=k2_relat_1(B_196) | k1_tarski(A_197)!=k1_relat_1(B_196) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.66/1.63  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.66/1.63  tff(c_780, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_22])).
% 3.66/1.63  tff(c_1053, plain, (![A_188, B_189, C_190]: (k2_relset_1(A_188, B_189, C_190)=k2_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.63  tff(c_1057, plain, (![A_188, B_189]: (k2_relset_1(A_188, B_189, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_780, c_1053])).
% 3.66/1.63  tff(c_1059, plain, (![A_188, B_189]: (k2_relset_1(A_188, B_189, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_784, c_1057])).
% 3.66/1.63  tff(c_1060, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_62])).
% 3.66/1.63  tff(c_1163, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_1060])).
% 3.66/1.63  tff(c_1172, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_70, c_785, c_784, c_1163])).
% 3.66/1.63  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.66/1.63  tff(c_782, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_8])).
% 3.66/1.63  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.63  tff(c_787, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_64])).
% 3.66/1.63  tff(c_68, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.66/1.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.63  tff(c_60, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.63  tff(c_1208, plain, (![D_204, C_205, A_206, B_207]: (r2_hidden(k1_funct_1(D_204, C_205), k2_relset_1(A_206, B_207, D_204)) | B_207='#skF_4' | ~r2_hidden(C_205, A_206) | ~m1_subset_1(D_204, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2(D_204, A_206, B_207) | ~v1_funct_1(D_204))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_60])).
% 3.66/1.63  tff(c_1216, plain, (![C_205, B_189, A_188]: (r2_hidden(k1_funct_1('#skF_4', C_205), '#skF_4') | B_189='#skF_4' | ~r2_hidden(C_205, A_188) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_2('#skF_4', A_188, B_189) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_1208])).
% 3.66/1.63  tff(c_1624, plain, (![C_239, B_240, A_241]: (r2_hidden(k1_funct_1('#skF_4', C_239), '#skF_4') | B_240='#skF_4' | ~r2_hidden(C_239, A_241) | ~v1_funct_2('#skF_4', A_241, B_240))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_780, c_1216])).
% 3.66/1.63  tff(c_1994, plain, (![A_255, B_256, B_257]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_255, B_256)), '#skF_4') | B_257='#skF_4' | ~v1_funct_2('#skF_4', A_255, B_257) | r1_tarski(A_255, B_256))), inference(resolution, [status(thm)], [c_6, c_1624])).
% 3.66/1.63  tff(c_1996, plain, (![B_256]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'), B_256)), '#skF_4') | '#skF_3'='#skF_4' | r1_tarski(k1_tarski('#skF_2'), B_256))), inference(resolution, [status(thm)], [c_68, c_1994])).
% 3.66/1.63  tff(c_2047, plain, (![B_261]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'), B_261)), '#skF_4') | r1_tarski(k1_tarski('#skF_2'), B_261))), inference(negUnitSimplification, [status(thm)], [c_787, c_1996])).
% 3.66/1.63  tff(c_50, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.63  tff(c_2056, plain, (![B_261]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'), B_261))) | r1_tarski(k1_tarski('#skF_2'), B_261))), inference(resolution, [status(thm)], [c_2047, c_50])).
% 3.66/1.63  tff(c_2066, plain, (![B_262]: (r1_tarski(k1_tarski('#skF_2'), B_262))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_2056])).
% 3.66/1.63  tff(c_891, plain, (![C_157, A_158, B_159]: (v4_relat_1(C_157, A_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.66/1.63  tff(c_896, plain, (![A_158]: (v4_relat_1('#skF_4', A_158))), inference(resolution, [status(thm)], [c_780, c_891])).
% 3.66/1.63  tff(c_942, plain, (![B_169, A_170]: (k7_relat_1(B_169, A_170)=B_169 | ~v4_relat_1(B_169, A_170) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.63  tff(c_948, plain, (![A_158]: (k7_relat_1('#skF_4', A_158)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_896, c_942])).
% 3.66/1.63  tff(c_952, plain, (![A_158]: (k7_relat_1('#skF_4', A_158)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_948])).
% 3.66/1.63  tff(c_1014, plain, (![B_185, A_186]: (k1_relat_1(k7_relat_1(B_185, A_186))=A_186 | ~r1_tarski(A_186, k1_relat_1(B_185)) | ~v1_relat_1(B_185))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.66/1.63  tff(c_1029, plain, (![A_186]: (k1_relat_1(k7_relat_1('#skF_4', A_186))=A_186 | ~r1_tarski(A_186, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_785, c_1014])).
% 3.66/1.63  tff(c_1034, plain, (![A_186]: (A_186='#skF_4' | ~r1_tarski(A_186, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_785, c_952, c_1029])).
% 3.66/1.63  tff(c_2085, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_2066, c_1034])).
% 3.66/1.63  tff(c_2109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1172, c_2085])).
% 3.66/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  Inference rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Ref     : 0
% 3.66/1.63  #Sup     : 462
% 3.66/1.63  #Fact    : 0
% 3.66/1.63  #Define  : 0
% 3.66/1.63  #Split   : 2
% 3.66/1.63  #Chain   : 0
% 3.66/1.63  #Close   : 0
% 3.66/1.63  
% 3.66/1.63  Ordering : KBO
% 3.66/1.63  
% 3.66/1.63  Simplification rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Subsume      : 80
% 3.66/1.63  #Demod        : 295
% 3.66/1.63  #Tautology    : 183
% 3.66/1.63  #SimpNegUnit  : 4
% 3.66/1.63  #BackRed      : 27
% 3.66/1.63  
% 3.66/1.63  #Partial instantiations: 0
% 3.66/1.63  #Strategies tried      : 1
% 3.66/1.63  
% 3.66/1.63  Timing (in seconds)
% 3.66/1.63  ----------------------
% 3.66/1.63  Preprocessing        : 0.33
% 3.66/1.63  Parsing              : 0.18
% 3.66/1.63  CNF conversion       : 0.02
% 4.08/1.63  Main loop            : 0.55
% 4.08/1.63  Inferencing          : 0.19
% 4.08/1.63  Reduction            : 0.18
% 4.08/1.63  Demodulation         : 0.13
% 4.08/1.63  BG Simplification    : 0.03
% 4.08/1.63  Subsumption          : 0.11
% 4.08/1.63  Abstraction          : 0.02
% 4.08/1.63  MUC search           : 0.00
% 4.08/1.63  Cooper               : 0.00
% 4.08/1.63  Total                : 0.92
% 4.08/1.63  Index Insertion      : 0.00
% 4.08/1.63  Index Deletion       : 0.00
% 4.08/1.63  Index Matching       : 0.00
% 4.08/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
