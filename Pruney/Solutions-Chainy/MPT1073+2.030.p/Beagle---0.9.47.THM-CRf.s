%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 179 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 400 expanded)
%              Number of equality atoms :   36 ( 102 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_166,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_180,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_166])).

tff(c_52,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_183,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_63])).

tff(c_86,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_20,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_521,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k7_relset_1(A_135,B_136,C_137,D_138) = k9_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_537,plain,(
    ! [D_139] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_139) = k9_relat_1('#skF_6',D_139) ),
    inference(resolution,[status(thm)],[c_54,c_521])).

tff(c_30,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( m1_subset_1(k7_relset_1(A_24,B_25,C_26,D_27),k1_zfmisc_1(B_25))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_543,plain,(
    ! [D_139] :
      ( m1_subset_1(k9_relat_1('#skF_6',D_139),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_30])).

tff(c_567,plain,(
    ! [D_142] : m1_subset_1(k9_relat_1('#skF_6',D_142),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_543])).

tff(c_574,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_567])).

tff(c_577,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_574])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [C_54,A_55,B_56] :
      ( r2_hidden(C_54,A_55)
      | ~ r2_hidden(C_54,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_57,A_58] :
      ( r2_hidden('#skF_1'(A_57),A_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(A_58))
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_123,plain,(
    ! [A_58,A_57] :
      ( ~ v1_xboole_0(A_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(A_58))
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_583,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_577,c_123])).

tff(c_587,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_583])).

tff(c_184,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_52])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_202,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_216,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_202])).

tff(c_1183,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1198,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1183])).

tff(c_1204,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_216,c_1198])).

tff(c_1205,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1204])).

tff(c_1232,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_20])).

tff(c_1250,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1232])).

tff(c_245,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_2'(A_84,B_85,C_86),B_85)
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_255,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_2'(A_84,B_85,C_86),B_85)
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_245,c_10])).

tff(c_1298,plain,(
    ! [A_84] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_84,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_255])).

tff(c_1347,plain,(
    ! [A_233] :
      ( m1_subset_1('#skF_2'(A_233,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_233,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1298])).

tff(c_1374,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_1347])).

tff(c_50,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_6',E_42) != '#skF_3'
      | ~ m1_subset_1(E_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1382,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1374,c_50])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_602,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_2'(A_150,B_151,C_152),A_150),C_152)
      | ~ r2_hidden(A_150,k9_relat_1(C_152,B_151))
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2112,plain,(
    ! [C_274,A_275,B_276] :
      ( k1_funct_1(C_274,'#skF_2'(A_275,B_276,C_274)) = A_275
      | ~ v1_funct_1(C_274)
      | ~ r2_hidden(A_275,k9_relat_1(C_274,B_276))
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_602,c_24])).

tff(c_2114,plain,(
    ! [A_275] :
      ( k1_funct_1('#skF_6','#skF_2'(A_275,'#skF_4','#skF_6')) = A_275
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_275,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_2112])).

tff(c_2139,plain,(
    ! [A_277] :
      ( k1_funct_1('#skF_6','#skF_2'(A_277,'#skF_4','#skF_6')) = A_277
      | ~ r2_hidden(A_277,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_58,c_2114])).

tff(c_2154,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_184,c_2139])).

tff(c_2169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1382,c_2154])).

tff(c_2170,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2177,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2170,c_6])).

tff(c_2179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_587,c_2177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.86  
% 4.51/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.86  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.51/1.86  
% 4.51/1.86  %Foreground sorts:
% 4.51/1.86  
% 4.51/1.86  
% 4.51/1.86  %Background operators:
% 4.51/1.86  
% 4.51/1.86  
% 4.51/1.86  %Foreground operators:
% 4.51/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.51/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.51/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.51/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.51/1.86  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.51/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.86  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.51/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.51/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.51/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.51/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.86  
% 4.51/1.88  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 4.51/1.88  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.51/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.51/1.88  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.88  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 4.51/1.88  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.51/1.88  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.51/1.88  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.51/1.88  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.88  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.88  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.51/1.88  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.51/1.88  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.51/1.88  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.51/1.88  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.51/1.88  tff(c_166, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.51/1.88  tff(c_180, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_166])).
% 4.51/1.88  tff(c_52, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.51/1.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.88  tff(c_63, plain, (~v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 4.51/1.88  tff(c_183, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_63])).
% 4.51/1.88  tff(c_86, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.51/1.88  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_86])).
% 4.51/1.88  tff(c_20, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.88  tff(c_521, plain, (![A_135, B_136, C_137, D_138]: (k7_relset_1(A_135, B_136, C_137, D_138)=k9_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.51/1.88  tff(c_537, plain, (![D_139]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_139)=k9_relat_1('#skF_6', D_139))), inference(resolution, [status(thm)], [c_54, c_521])).
% 4.51/1.88  tff(c_30, plain, (![A_24, B_25, C_26, D_27]: (m1_subset_1(k7_relset_1(A_24, B_25, C_26, D_27), k1_zfmisc_1(B_25)) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.88  tff(c_543, plain, (![D_139]: (m1_subset_1(k9_relat_1('#skF_6', D_139), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_537, c_30])).
% 4.51/1.88  tff(c_567, plain, (![D_142]: (m1_subset_1(k9_relat_1('#skF_6', D_142), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_543])).
% 4.51/1.88  tff(c_574, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20, c_567])).
% 4.51/1.88  tff(c_577, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_574])).
% 4.51/1.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.88  tff(c_105, plain, (![C_54, A_55, B_56]: (r2_hidden(C_54, A_55) | ~r2_hidden(C_54, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.88  tff(c_112, plain, (![A_57, A_58]: (r2_hidden('#skF_1'(A_57), A_58) | ~m1_subset_1(A_57, k1_zfmisc_1(A_58)) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_4, c_105])).
% 4.51/1.88  tff(c_123, plain, (![A_58, A_57]: (~v1_xboole_0(A_58) | ~m1_subset_1(A_57, k1_zfmisc_1(A_58)) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_112, c_2])).
% 4.51/1.88  tff(c_583, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_577, c_123])).
% 4.51/1.88  tff(c_587, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_183, c_583])).
% 4.51/1.88  tff(c_184, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_52])).
% 4.51/1.88  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.51/1.88  tff(c_202, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.51/1.88  tff(c_216, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_202])).
% 4.51/1.88  tff(c_1183, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.88  tff(c_1198, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_1183])).
% 4.51/1.88  tff(c_1204, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_216, c_1198])).
% 4.51/1.88  tff(c_1205, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1204])).
% 4.51/1.88  tff(c_1232, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1205, c_20])).
% 4.51/1.88  tff(c_1250, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1232])).
% 4.51/1.88  tff(c_245, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_2'(A_84, B_85, C_86), B_85) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.88  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.51/1.88  tff(c_255, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_2'(A_84, B_85, C_86), B_85) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_245, c_10])).
% 4.51/1.88  tff(c_1298, plain, (![A_84]: (m1_subset_1('#skF_2'(A_84, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_84, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1250, c_255])).
% 4.51/1.88  tff(c_1347, plain, (![A_233]: (m1_subset_1('#skF_2'(A_233, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_233, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1298])).
% 4.51/1.88  tff(c_1374, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_184, c_1347])).
% 4.51/1.88  tff(c_50, plain, (![E_42]: (k1_funct_1('#skF_6', E_42)!='#skF_3' | ~m1_subset_1(E_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.51/1.88  tff(c_1382, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_1374, c_50])).
% 4.51/1.88  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.51/1.88  tff(c_602, plain, (![A_150, B_151, C_152]: (r2_hidden(k4_tarski('#skF_2'(A_150, B_151, C_152), A_150), C_152) | ~r2_hidden(A_150, k9_relat_1(C_152, B_151)) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.88  tff(c_24, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.51/1.88  tff(c_2112, plain, (![C_274, A_275, B_276]: (k1_funct_1(C_274, '#skF_2'(A_275, B_276, C_274))=A_275 | ~v1_funct_1(C_274) | ~r2_hidden(A_275, k9_relat_1(C_274, B_276)) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_602, c_24])).
% 4.51/1.88  tff(c_2114, plain, (![A_275]: (k1_funct_1('#skF_6', '#skF_2'(A_275, '#skF_4', '#skF_6'))=A_275 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_275, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1250, c_2112])).
% 4.51/1.88  tff(c_2139, plain, (![A_277]: (k1_funct_1('#skF_6', '#skF_2'(A_277, '#skF_4', '#skF_6'))=A_277 | ~r2_hidden(A_277, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_58, c_2114])).
% 4.51/1.88  tff(c_2154, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(resolution, [status(thm)], [c_184, c_2139])).
% 4.51/1.88  tff(c_2169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1382, c_2154])).
% 4.51/1.88  tff(c_2170, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1204])).
% 4.51/1.88  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.88  tff(c_2177, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2170, c_6])).
% 4.51/1.88  tff(c_2179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_587, c_2177])).
% 4.51/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.88  
% 4.51/1.88  Inference rules
% 4.51/1.88  ----------------------
% 4.51/1.88  #Ref     : 0
% 4.51/1.88  #Sup     : 438
% 4.51/1.88  #Fact    : 0
% 4.51/1.88  #Define  : 0
% 4.51/1.88  #Split   : 5
% 4.51/1.88  #Chain   : 0
% 4.51/1.88  #Close   : 0
% 4.51/1.88  
% 4.51/1.88  Ordering : KBO
% 4.51/1.88  
% 4.51/1.88  Simplification rules
% 4.51/1.88  ----------------------
% 4.51/1.88  #Subsume      : 58
% 4.51/1.88  #Demod        : 106
% 4.51/1.88  #Tautology    : 23
% 4.51/1.88  #SimpNegUnit  : 12
% 4.51/1.88  #BackRed      : 12
% 4.51/1.88  
% 4.51/1.88  #Partial instantiations: 0
% 4.51/1.88  #Strategies tried      : 1
% 4.51/1.88  
% 4.51/1.88  Timing (in seconds)
% 4.51/1.88  ----------------------
% 4.51/1.88  Preprocessing        : 0.33
% 4.51/1.88  Parsing              : 0.17
% 4.51/1.88  CNF conversion       : 0.02
% 4.51/1.88  Main loop            : 0.71
% 4.51/1.88  Inferencing          : 0.24
% 4.51/1.88  Reduction            : 0.20
% 4.51/1.88  Demodulation         : 0.14
% 4.51/1.88  BG Simplification    : 0.03
% 4.51/1.89  Subsumption          : 0.17
% 4.51/1.89  Abstraction          : 0.04
% 4.51/1.89  MUC search           : 0.00
% 4.51/1.89  Cooper               : 0.00
% 4.51/1.89  Total                : 1.07
% 4.51/1.89  Index Insertion      : 0.00
% 4.51/1.89  Index Deletion       : 0.00
% 4.51/1.89  Index Matching       : 0.00
% 4.51/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
