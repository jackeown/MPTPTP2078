%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 6.83s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 408 expanded)
%              Number of leaves         :   37 ( 153 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 (1100 expanded)
%              Number of equality atoms :   26 ( 129 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                      <=> ? [F] :
                            ( m1_subset_1(F,C)
                            & r2_hidden(k4_tarski(F,E),D)
                            & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_96,plain,(
    ! [C_150,A_151,B_152] :
      ( v1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_107,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden('#skF_2'(A_179,B_180,C_181),B_180)
      | ~ r2_hidden(A_179,k9_relat_1(C_181,B_180))
      | ~ v1_relat_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [B_184,A_185,C_186] :
      ( ~ v1_xboole_0(B_184)
      | ~ r2_hidden(A_185,k9_relat_1(C_186,B_184))
      | ~ v1_relat_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_231,c_2])).

tff(c_277,plain,(
    ! [B_184,C_186] :
      ( ~ v1_xboole_0(B_184)
      | ~ v1_relat_1(C_186)
      | v1_xboole_0(k9_relat_1(C_186,B_184)) ) ),
    inference(resolution,[status(thm)],[c_4,c_262])).

tff(c_376,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k7_relset_1(A_216,B_217,C_218,D_219) = k9_relat_1(C_218,D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_393,plain,(
    ! [D_219] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_219) = k9_relat_1('#skF_7',D_219) ),
    inference(resolution,[status(thm)],[c_50,c_376])).

tff(c_48,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_75,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_395,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_75])).

tff(c_416,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_277,c_395])).

tff(c_422,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_416])).

tff(c_396,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_48])).

tff(c_397,plain,(
    ! [D_220] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_220) = k9_relat_1('#skF_7',D_220) ),
    inference(resolution,[status(thm)],[c_50,c_376])).

tff(c_34,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( m1_subset_1(k7_relset_1(A_33,B_34,C_35,D_36),k1_zfmisc_1(B_34))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_403,plain,(
    ! [D_220] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_220),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_34])).

tff(c_511,plain,(
    ! [D_223] : m1_subset_1(k9_relat_1('#skF_7',D_223),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_403])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_571,plain,(
    ! [A_227,D_228] :
      ( m1_subset_1(A_227,'#skF_5')
      | ~ r2_hidden(A_227,k9_relat_1('#skF_7',D_228)) ) ),
    inference(resolution,[status(thm)],[c_511,c_12])).

tff(c_596,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_571])).

tff(c_141,plain,(
    ! [C_164,B_165,A_166] :
      ( v1_xboole_0(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(B_165,A_166)))
      | ~ v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_152,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_141])).

tff(c_153,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_108,plain,(
    ! [C_153,A_154,B_155] :
      ( v1_xboole_0(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_120,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_808,plain,(
    ! [D_257,E_255,B_256,C_253,A_254] :
      ( m1_subset_1('#skF_3'(C_253,A_254,E_255,B_256,D_257),C_253)
      | ~ r2_hidden(E_255,k7_relset_1(C_253,A_254,D_257,B_256))
      | ~ m1_subset_1(E_255,A_254)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(C_253,A_254)))
      | v1_xboole_0(C_253)
      | v1_xboole_0(B_256)
      | v1_xboole_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_816,plain,(
    ! [E_255,D_219] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_255,D_219,'#skF_7'),'#skF_4')
      | ~ r2_hidden(E_255,k9_relat_1('#skF_7',D_219))
      | ~ m1_subset_1(E_255,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_219)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_808])).

tff(c_829,plain,(
    ! [E_255,D_219] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_255,D_219,'#skF_7'),'#skF_4')
      | ~ r2_hidden(E_255,k9_relat_1('#skF_7',D_219))
      | ~ m1_subset_1(E_255,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_219)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_816])).

tff(c_2477,plain,(
    ! [E_443,D_444] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_443,D_444,'#skF_7'),'#skF_4')
      | ~ r2_hidden(E_443,k9_relat_1('#skF_7',D_444))
      | ~ m1_subset_1(E_443,'#skF_5')
      | v1_xboole_0(D_444) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_120,c_829])).

tff(c_2499,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_396,c_2477])).

tff(c_2528,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_2499])).

tff(c_2529,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_2528])).

tff(c_932,plain,(
    ! [A_279,B_281,C_278,D_282,E_280] :
      ( r2_hidden('#skF_3'(C_278,A_279,E_280,B_281,D_282),B_281)
      | ~ r2_hidden(E_280,k7_relset_1(C_278,A_279,D_282,B_281))
      | ~ m1_subset_1(E_280,A_279)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(C_278,A_279)))
      | v1_xboole_0(C_278)
      | v1_xboole_0(B_281)
      | v1_xboole_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_943,plain,(
    ! [E_280,B_281] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',E_280,B_281,'#skF_7'),B_281)
      | ~ r2_hidden(E_280,k7_relset_1('#skF_4','#skF_5','#skF_7',B_281))
      | ~ m1_subset_1(E_280,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_281)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_932])).

tff(c_950,plain,(
    ! [E_280,B_281] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',E_280,B_281,'#skF_7'),B_281)
      | ~ r2_hidden(E_280,k9_relat_1('#skF_7',B_281))
      | ~ m1_subset_1(E_280,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_281)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_943])).

tff(c_1822,plain,(
    ! [E_395,B_396] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',E_395,B_396,'#skF_7'),B_396)
      | ~ r2_hidden(E_395,k9_relat_1('#skF_7',B_396))
      | ~ m1_subset_1(E_395,'#skF_5')
      | v1_xboole_0(B_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_120,c_950])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2915,plain,(
    ! [E_461,B_462] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_461,B_462,'#skF_7'),B_462)
      | ~ r2_hidden(E_461,k9_relat_1('#skF_7',B_462))
      | ~ m1_subset_1(E_461,'#skF_5')
      | v1_xboole_0(B_462) ) ),
    inference(resolution,[status(thm)],[c_1822,c_8])).

tff(c_2933,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_396,c_2915])).

tff(c_2962,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_2933])).

tff(c_2963,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_2962])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    ! [A_148,B_149] :
      ( r2_hidden(A_148,B_149)
      | v1_xboole_0(B_149)
      | ~ m1_subset_1(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [F_139] :
      ( k1_funct_1('#skF_7',F_139) != '#skF_8'
      | ~ r2_hidden(F_139,'#skF_6')
      | ~ r2_hidden(F_139,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_93,plain,(
    ! [A_148] :
      ( k1_funct_1('#skF_7',A_148) != '#skF_8'
      | ~ r2_hidden(A_148,'#skF_4')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_148,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_46])).

tff(c_167,plain,(
    ! [A_171] :
      ( k1_funct_1('#skF_7',A_171) != '#skF_8'
      | ~ r2_hidden(A_171,'#skF_4')
      | ~ m1_subset_1(A_171,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_171,plain,(
    ! [A_8] :
      ( k1_funct_1('#skF_7',A_8) != '#skF_8'
      | ~ m1_subset_1(A_8,'#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_178,plain,(
    ! [A_8] :
      ( k1_funct_1('#skF_7',A_8) != '#skF_8'
      | ~ m1_subset_1(A_8,'#skF_6')
      | ~ m1_subset_1(A_8,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_171])).

tff(c_2970,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2963,c_178])).

tff(c_2973,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2529,c_2970])).

tff(c_1169,plain,(
    ! [E_305,D_307,A_304,B_306,C_303] :
      ( r2_hidden(k4_tarski('#skF_3'(C_303,A_304,E_305,B_306,D_307),E_305),D_307)
      | ~ r2_hidden(E_305,k7_relset_1(C_303,A_304,D_307,B_306))
      | ~ m1_subset_1(E_305,A_304)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(C_303,A_304)))
      | v1_xboole_0(C_303)
      | v1_xboole_0(B_306)
      | v1_xboole_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4620,plain,(
    ! [C_588,D_585,E_589,B_586,A_587] :
      ( k1_funct_1(D_585,'#skF_3'(C_588,A_587,E_589,B_586,D_585)) = E_589
      | ~ v1_funct_1(D_585)
      | ~ v1_relat_1(D_585)
      | ~ r2_hidden(E_589,k7_relset_1(C_588,A_587,D_585,B_586))
      | ~ m1_subset_1(E_589,A_587)
      | ~ m1_subset_1(D_585,k1_zfmisc_1(k2_zfmisc_1(C_588,A_587)))
      | v1_xboole_0(C_588)
      | v1_xboole_0(B_586)
      | v1_xboole_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_1169,c_24])).

tff(c_4636,plain,(
    ! [E_589,D_219] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_589,D_219,'#skF_7')) = E_589
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_589,k9_relat_1('#skF_7',D_219))
      | ~ m1_subset_1(E_589,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_219)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_4620])).

tff(c_4653,plain,(
    ! [E_589,D_219] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_589,D_219,'#skF_7')) = E_589
      | ~ r2_hidden(E_589,k9_relat_1('#skF_7',D_219))
      | ~ m1_subset_1(E_589,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_219)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_107,c_54,c_4636])).

tff(c_4658,plain,(
    ! [E_590,D_591] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_590,D_591,'#skF_7')) = E_590
      | ~ r2_hidden(E_590,k9_relat_1('#skF_7',D_591))
      | ~ m1_subset_1(E_590,'#skF_5')
      | v1_xboole_0(D_591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_120,c_4653])).

tff(c_4695,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_396,c_4658])).

tff(c_4738,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_4695])).

tff(c_4740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_2973,c_4738])).

tff(c_4741,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4780,plain,(
    ! [A_600,B_601,C_602] :
      ( r2_hidden('#skF_2'(A_600,B_601,C_602),B_601)
      | ~ r2_hidden(A_600,k9_relat_1(C_602,B_601))
      | ~ v1_relat_1(C_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4799,plain,(
    ! [B_603,A_604,C_605] :
      ( ~ v1_xboole_0(B_603)
      | ~ r2_hidden(A_604,k9_relat_1(C_605,B_603))
      | ~ v1_relat_1(C_605) ) ),
    inference(resolution,[status(thm)],[c_4780,c_2])).

tff(c_4814,plain,(
    ! [B_603,C_605] :
      ( ~ v1_xboole_0(B_603)
      | ~ v1_relat_1(C_605)
      | v1_xboole_0(k9_relat_1(C_605,B_603)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4799])).

tff(c_4859,plain,(
    ! [A_623,B_624,C_625,D_626] :
      ( k7_relset_1(A_623,B_624,C_625,D_626) = k9_relat_1(C_625,D_626)
      | ~ m1_subset_1(C_625,k1_zfmisc_1(k2_zfmisc_1(A_623,B_624))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4872,plain,(
    ! [D_626] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_626) = k9_relat_1('#skF_7',D_626) ),
    inference(resolution,[status(thm)],[c_50,c_4859])).

tff(c_4874,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_75])).

tff(c_4887,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4814,c_4874])).

tff(c_4891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_4741,c_4887])).

tff(c_4892,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_5235,plain,(
    ! [A_686,C_687] :
      ( r2_hidden(k4_tarski(A_686,k1_funct_1(C_687,A_686)),C_687)
      | ~ r2_hidden(A_686,k1_relat_1(C_687))
      | ~ v1_funct_1(C_687)
      | ~ v1_relat_1(C_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5304,plain,(
    ! [C_690,A_691] :
      ( ~ v1_xboole_0(C_690)
      | ~ r2_hidden(A_691,k1_relat_1(C_690))
      | ~ v1_funct_1(C_690)
      | ~ v1_relat_1(C_690) ) ),
    inference(resolution,[status(thm)],[c_5235,c_2])).

tff(c_5329,plain,(
    ! [C_692] :
      ( ~ v1_xboole_0(C_692)
      | ~ v1_funct_1(C_692)
      | ~ v1_relat_1(C_692)
      | v1_xboole_0(k1_relat_1(C_692)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5304])).

tff(c_5055,plain,(
    ! [A_663,B_664,C_665,D_666] :
      ( k7_relset_1(A_663,B_664,C_665,D_666) = k9_relat_1(C_665,D_666)
      | ~ m1_subset_1(C_665,k1_zfmisc_1(k2_zfmisc_1(A_663,B_664))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5068,plain,(
    ! [D_666] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_666) = k9_relat_1('#skF_7',D_666) ),
    inference(resolution,[status(thm)],[c_50,c_5055])).

tff(c_5071,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5068,c_48])).

tff(c_5204,plain,(
    ! [A_680,B_681,C_682] :
      ( r2_hidden('#skF_2'(A_680,B_681,C_682),k1_relat_1(C_682))
      | ~ r2_hidden(A_680,k9_relat_1(C_682,B_681))
      | ~ v1_relat_1(C_682) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5213,plain,(
    ! [C_683,A_684,B_685] :
      ( ~ v1_xboole_0(k1_relat_1(C_683))
      | ~ r2_hidden(A_684,k9_relat_1(C_683,B_685))
      | ~ v1_relat_1(C_683) ) ),
    inference(resolution,[status(thm)],[c_5204,c_2])).

tff(c_5216,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5071,c_5213])).

tff(c_5231,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_5216])).

tff(c_5332,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5329,c_5231])).

tff(c_5336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_54,c_4892,c_5332])).

tff(c_5337,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_5562,plain,(
    ! [A_750,B_751,C_752,D_753] :
      ( k7_relset_1(A_750,B_751,C_752,D_753) = k9_relat_1(C_752,D_753)
      | ~ m1_subset_1(C_752,k1_zfmisc_1(k2_zfmisc_1(A_750,B_751))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5579,plain,(
    ! [D_753] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_753) = k9_relat_1('#skF_7',D_753) ),
    inference(resolution,[status(thm)],[c_50,c_5562])).

tff(c_5582,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5579,c_48])).

tff(c_5635,plain,(
    ! [A_755,B_756,C_757] :
      ( r2_hidden(k4_tarski('#skF_2'(A_755,B_756,C_757),A_755),C_757)
      | ~ r2_hidden(A_755,k9_relat_1(C_757,B_756))
      | ~ v1_relat_1(C_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5716,plain,(
    ! [C_761,A_762,B_763] :
      ( ~ v1_xboole_0(C_761)
      | ~ r2_hidden(A_762,k9_relat_1(C_761,B_763))
      | ~ v1_relat_1(C_761) ) ),
    inference(resolution,[status(thm)],[c_5635,c_2])).

tff(c_5723,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5582,c_5716])).

tff(c_5740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_5337,c_5723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:24:21 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.83/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.83/2.47  
% 6.83/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.83/2.47  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 6.83/2.47  
% 6.83/2.47  %Foreground sorts:
% 6.83/2.47  
% 6.83/2.47  
% 6.83/2.47  %Background operators:
% 6.83/2.47  
% 6.83/2.47  
% 6.83/2.47  %Foreground operators:
% 6.83/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.83/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.83/2.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.83/2.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.83/2.47  tff('#skF_7', type, '#skF_7': $i).
% 6.83/2.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.83/2.47  tff('#skF_5', type, '#skF_5': $i).
% 6.83/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.83/2.47  tff('#skF_6', type, '#skF_6': $i).
% 6.83/2.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.83/2.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.83/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.83/2.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.83/2.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 6.83/2.47  tff('#skF_8', type, '#skF_8': $i).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.83/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.83/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.83/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.83/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.83/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.83/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.83/2.47  
% 6.83/2.49  tff(f_142, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 6.83/2.49  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.83/2.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.83/2.49  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 6.83/2.49  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.83/2.49  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 6.83/2.49  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.83/2.49  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.83/2.49  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.83/2.49  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 6.83/2.49  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.83/2.49  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.83/2.49  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 6.83/2.49  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.83/2.49  tff(c_96, plain, (![C_150, A_151, B_152]: (v1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.83/2.49  tff(c_107, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_96])).
% 6.83/2.49  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.83/2.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.83/2.49  tff(c_231, plain, (![A_179, B_180, C_181]: (r2_hidden('#skF_2'(A_179, B_180, C_181), B_180) | ~r2_hidden(A_179, k9_relat_1(C_181, B_180)) | ~v1_relat_1(C_181))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.83/2.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.83/2.49  tff(c_262, plain, (![B_184, A_185, C_186]: (~v1_xboole_0(B_184) | ~r2_hidden(A_185, k9_relat_1(C_186, B_184)) | ~v1_relat_1(C_186))), inference(resolution, [status(thm)], [c_231, c_2])).
% 6.83/2.49  tff(c_277, plain, (![B_184, C_186]: (~v1_xboole_0(B_184) | ~v1_relat_1(C_186) | v1_xboole_0(k9_relat_1(C_186, B_184)))), inference(resolution, [status(thm)], [c_4, c_262])).
% 6.83/2.49  tff(c_376, plain, (![A_216, B_217, C_218, D_219]: (k7_relset_1(A_216, B_217, C_218, D_219)=k9_relat_1(C_218, D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.83/2.49  tff(c_393, plain, (![D_219]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_219)=k9_relat_1('#skF_7', D_219))), inference(resolution, [status(thm)], [c_50, c_376])).
% 6.83/2.49  tff(c_48, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.83/2.49  tff(c_75, plain, (~v1_xboole_0(k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 6.83/2.49  tff(c_395, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_75])).
% 6.83/2.49  tff(c_416, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_277, c_395])).
% 6.83/2.49  tff(c_422, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_416])).
% 6.83/2.49  tff(c_396, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_48])).
% 6.83/2.49  tff(c_397, plain, (![D_220]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_220)=k9_relat_1('#skF_7', D_220))), inference(resolution, [status(thm)], [c_50, c_376])).
% 6.83/2.49  tff(c_34, plain, (![A_33, B_34, C_35, D_36]: (m1_subset_1(k7_relset_1(A_33, B_34, C_35, D_36), k1_zfmisc_1(B_34)) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.83/2.49  tff(c_403, plain, (![D_220]: (m1_subset_1(k9_relat_1('#skF_7', D_220), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_397, c_34])).
% 6.83/2.49  tff(c_511, plain, (![D_223]: (m1_subset_1(k9_relat_1('#skF_7', D_223), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_403])).
% 6.83/2.49  tff(c_12, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.83/2.49  tff(c_571, plain, (![A_227, D_228]: (m1_subset_1(A_227, '#skF_5') | ~r2_hidden(A_227, k9_relat_1('#skF_7', D_228)))), inference(resolution, [status(thm)], [c_511, c_12])).
% 6.83/2.49  tff(c_596, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_396, c_571])).
% 6.83/2.49  tff(c_141, plain, (![C_164, B_165, A_166]: (v1_xboole_0(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(B_165, A_166))) | ~v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.83/2.49  tff(c_152, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_141])).
% 6.83/2.49  tff(c_153, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_152])).
% 6.83/2.49  tff(c_108, plain, (![C_153, A_154, B_155]: (v1_xboole_0(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.83/2.49  tff(c_119, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_108])).
% 6.83/2.49  tff(c_120, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_119])).
% 6.83/2.49  tff(c_808, plain, (![D_257, E_255, B_256, C_253, A_254]: (m1_subset_1('#skF_3'(C_253, A_254, E_255, B_256, D_257), C_253) | ~r2_hidden(E_255, k7_relset_1(C_253, A_254, D_257, B_256)) | ~m1_subset_1(E_255, A_254) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(C_253, A_254))) | v1_xboole_0(C_253) | v1_xboole_0(B_256) | v1_xboole_0(A_254))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.83/2.49  tff(c_816, plain, (![E_255, D_219]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_255, D_219, '#skF_7'), '#skF_4') | ~r2_hidden(E_255, k9_relat_1('#skF_7', D_219)) | ~m1_subset_1(E_255, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_219) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_808])).
% 6.83/2.49  tff(c_829, plain, (![E_255, D_219]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_255, D_219, '#skF_7'), '#skF_4') | ~r2_hidden(E_255, k9_relat_1('#skF_7', D_219)) | ~m1_subset_1(E_255, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_219) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_816])).
% 6.83/2.49  tff(c_2477, plain, (![E_443, D_444]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_443, D_444, '#skF_7'), '#skF_4') | ~r2_hidden(E_443, k9_relat_1('#skF_7', D_444)) | ~m1_subset_1(E_443, '#skF_5') | v1_xboole_0(D_444))), inference(negUnitSimplification, [status(thm)], [c_153, c_120, c_829])).
% 6.83/2.49  tff(c_2499, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_396, c_2477])).
% 6.83/2.49  tff(c_2528, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_2499])).
% 6.83/2.49  tff(c_2529, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_422, c_2528])).
% 6.83/2.49  tff(c_932, plain, (![A_279, B_281, C_278, D_282, E_280]: (r2_hidden('#skF_3'(C_278, A_279, E_280, B_281, D_282), B_281) | ~r2_hidden(E_280, k7_relset_1(C_278, A_279, D_282, B_281)) | ~m1_subset_1(E_280, A_279) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(C_278, A_279))) | v1_xboole_0(C_278) | v1_xboole_0(B_281) | v1_xboole_0(A_279))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.83/2.49  tff(c_943, plain, (![E_280, B_281]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', E_280, B_281, '#skF_7'), B_281) | ~r2_hidden(E_280, k7_relset_1('#skF_4', '#skF_5', '#skF_7', B_281)) | ~m1_subset_1(E_280, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_281) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_932])).
% 6.83/2.49  tff(c_950, plain, (![E_280, B_281]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', E_280, B_281, '#skF_7'), B_281) | ~r2_hidden(E_280, k9_relat_1('#skF_7', B_281)) | ~m1_subset_1(E_280, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_281) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_943])).
% 6.83/2.49  tff(c_1822, plain, (![E_395, B_396]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', E_395, B_396, '#skF_7'), B_396) | ~r2_hidden(E_395, k9_relat_1('#skF_7', B_396)) | ~m1_subset_1(E_395, '#skF_5') | v1_xboole_0(B_396))), inference(negUnitSimplification, [status(thm)], [c_153, c_120, c_950])).
% 6.83/2.49  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.83/2.49  tff(c_2915, plain, (![E_461, B_462]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_461, B_462, '#skF_7'), B_462) | ~r2_hidden(E_461, k9_relat_1('#skF_7', B_462)) | ~m1_subset_1(E_461, '#skF_5') | v1_xboole_0(B_462))), inference(resolution, [status(thm)], [c_1822, c_8])).
% 6.83/2.49  tff(c_2933, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_396, c_2915])).
% 6.83/2.49  tff(c_2962, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_2933])).
% 6.83/2.49  tff(c_2963, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_422, c_2962])).
% 6.83/2.49  tff(c_10, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.83/2.49  tff(c_82, plain, (![A_148, B_149]: (r2_hidden(A_148, B_149) | v1_xboole_0(B_149) | ~m1_subset_1(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.83/2.49  tff(c_46, plain, (![F_139]: (k1_funct_1('#skF_7', F_139)!='#skF_8' | ~r2_hidden(F_139, '#skF_6') | ~r2_hidden(F_139, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.83/2.49  tff(c_93, plain, (![A_148]: (k1_funct_1('#skF_7', A_148)!='#skF_8' | ~r2_hidden(A_148, '#skF_4') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_148, '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_46])).
% 6.83/2.49  tff(c_167, plain, (![A_171]: (k1_funct_1('#skF_7', A_171)!='#skF_8' | ~r2_hidden(A_171, '#skF_4') | ~m1_subset_1(A_171, '#skF_6'))), inference(splitLeft, [status(thm)], [c_93])).
% 6.83/2.49  tff(c_171, plain, (![A_8]: (k1_funct_1('#skF_7', A_8)!='#skF_8' | ~m1_subset_1(A_8, '#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_167])).
% 6.83/2.49  tff(c_178, plain, (![A_8]: (k1_funct_1('#skF_7', A_8)!='#skF_8' | ~m1_subset_1(A_8, '#skF_6') | ~m1_subset_1(A_8, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_120, c_171])).
% 6.83/2.49  tff(c_2970, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_2963, c_178])).
% 6.83/2.49  tff(c_2973, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2529, c_2970])).
% 6.83/2.49  tff(c_1169, plain, (![E_305, D_307, A_304, B_306, C_303]: (r2_hidden(k4_tarski('#skF_3'(C_303, A_304, E_305, B_306, D_307), E_305), D_307) | ~r2_hidden(E_305, k7_relset_1(C_303, A_304, D_307, B_306)) | ~m1_subset_1(E_305, A_304) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(C_303, A_304))) | v1_xboole_0(C_303) | v1_xboole_0(B_306) | v1_xboole_0(A_304))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.83/2.49  tff(c_24, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.83/2.49  tff(c_4620, plain, (![C_588, D_585, E_589, B_586, A_587]: (k1_funct_1(D_585, '#skF_3'(C_588, A_587, E_589, B_586, D_585))=E_589 | ~v1_funct_1(D_585) | ~v1_relat_1(D_585) | ~r2_hidden(E_589, k7_relset_1(C_588, A_587, D_585, B_586)) | ~m1_subset_1(E_589, A_587) | ~m1_subset_1(D_585, k1_zfmisc_1(k2_zfmisc_1(C_588, A_587))) | v1_xboole_0(C_588) | v1_xboole_0(B_586) | v1_xboole_0(A_587))), inference(resolution, [status(thm)], [c_1169, c_24])).
% 6.83/2.49  tff(c_4636, plain, (![E_589, D_219]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_589, D_219, '#skF_7'))=E_589 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(E_589, k9_relat_1('#skF_7', D_219)) | ~m1_subset_1(E_589, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_219) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_4620])).
% 6.83/2.49  tff(c_4653, plain, (![E_589, D_219]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_589, D_219, '#skF_7'))=E_589 | ~r2_hidden(E_589, k9_relat_1('#skF_7', D_219)) | ~m1_subset_1(E_589, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_219) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_107, c_54, c_4636])).
% 6.83/2.49  tff(c_4658, plain, (![E_590, D_591]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_590, D_591, '#skF_7'))=E_590 | ~r2_hidden(E_590, k9_relat_1('#skF_7', D_591)) | ~m1_subset_1(E_590, '#skF_5') | v1_xboole_0(D_591))), inference(negUnitSimplification, [status(thm)], [c_153, c_120, c_4653])).
% 6.83/2.49  tff(c_4695, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_396, c_4658])).
% 6.83/2.49  tff(c_4738, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))='#skF_8' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_4695])).
% 6.83/2.49  tff(c_4740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_422, c_2973, c_4738])).
% 6.83/2.49  tff(c_4741, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_93])).
% 6.83/2.49  tff(c_4780, plain, (![A_600, B_601, C_602]: (r2_hidden('#skF_2'(A_600, B_601, C_602), B_601) | ~r2_hidden(A_600, k9_relat_1(C_602, B_601)) | ~v1_relat_1(C_602))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.83/2.49  tff(c_4799, plain, (![B_603, A_604, C_605]: (~v1_xboole_0(B_603) | ~r2_hidden(A_604, k9_relat_1(C_605, B_603)) | ~v1_relat_1(C_605))), inference(resolution, [status(thm)], [c_4780, c_2])).
% 6.83/2.49  tff(c_4814, plain, (![B_603, C_605]: (~v1_xboole_0(B_603) | ~v1_relat_1(C_605) | v1_xboole_0(k9_relat_1(C_605, B_603)))), inference(resolution, [status(thm)], [c_4, c_4799])).
% 6.83/2.49  tff(c_4859, plain, (![A_623, B_624, C_625, D_626]: (k7_relset_1(A_623, B_624, C_625, D_626)=k9_relat_1(C_625, D_626) | ~m1_subset_1(C_625, k1_zfmisc_1(k2_zfmisc_1(A_623, B_624))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.83/2.49  tff(c_4872, plain, (![D_626]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_626)=k9_relat_1('#skF_7', D_626))), inference(resolution, [status(thm)], [c_50, c_4859])).
% 6.83/2.49  tff(c_4874, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_75])).
% 6.83/2.49  tff(c_4887, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4814, c_4874])).
% 6.83/2.49  tff(c_4891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_4741, c_4887])).
% 6.83/2.49  tff(c_4892, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_152])).
% 6.83/2.49  tff(c_5235, plain, (![A_686, C_687]: (r2_hidden(k4_tarski(A_686, k1_funct_1(C_687, A_686)), C_687) | ~r2_hidden(A_686, k1_relat_1(C_687)) | ~v1_funct_1(C_687) | ~v1_relat_1(C_687))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.83/2.49  tff(c_5304, plain, (![C_690, A_691]: (~v1_xboole_0(C_690) | ~r2_hidden(A_691, k1_relat_1(C_690)) | ~v1_funct_1(C_690) | ~v1_relat_1(C_690))), inference(resolution, [status(thm)], [c_5235, c_2])).
% 6.83/2.49  tff(c_5329, plain, (![C_692]: (~v1_xboole_0(C_692) | ~v1_funct_1(C_692) | ~v1_relat_1(C_692) | v1_xboole_0(k1_relat_1(C_692)))), inference(resolution, [status(thm)], [c_4, c_5304])).
% 6.83/2.49  tff(c_5055, plain, (![A_663, B_664, C_665, D_666]: (k7_relset_1(A_663, B_664, C_665, D_666)=k9_relat_1(C_665, D_666) | ~m1_subset_1(C_665, k1_zfmisc_1(k2_zfmisc_1(A_663, B_664))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.83/2.49  tff(c_5068, plain, (![D_666]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_666)=k9_relat_1('#skF_7', D_666))), inference(resolution, [status(thm)], [c_50, c_5055])).
% 6.83/2.49  tff(c_5071, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5068, c_48])).
% 6.83/2.49  tff(c_5204, plain, (![A_680, B_681, C_682]: (r2_hidden('#skF_2'(A_680, B_681, C_682), k1_relat_1(C_682)) | ~r2_hidden(A_680, k9_relat_1(C_682, B_681)) | ~v1_relat_1(C_682))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.83/2.49  tff(c_5213, plain, (![C_683, A_684, B_685]: (~v1_xboole_0(k1_relat_1(C_683)) | ~r2_hidden(A_684, k9_relat_1(C_683, B_685)) | ~v1_relat_1(C_683))), inference(resolution, [status(thm)], [c_5204, c_2])).
% 6.83/2.49  tff(c_5216, plain, (~v1_xboole_0(k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5071, c_5213])).
% 6.83/2.49  tff(c_5231, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_5216])).
% 6.83/2.49  tff(c_5332, plain, (~v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5329, c_5231])).
% 6.83/2.49  tff(c_5336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_54, c_4892, c_5332])).
% 6.83/2.49  tff(c_5337, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_119])).
% 6.83/2.49  tff(c_5562, plain, (![A_750, B_751, C_752, D_753]: (k7_relset_1(A_750, B_751, C_752, D_753)=k9_relat_1(C_752, D_753) | ~m1_subset_1(C_752, k1_zfmisc_1(k2_zfmisc_1(A_750, B_751))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.83/2.49  tff(c_5579, plain, (![D_753]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_753)=k9_relat_1('#skF_7', D_753))), inference(resolution, [status(thm)], [c_50, c_5562])).
% 6.83/2.49  tff(c_5582, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5579, c_48])).
% 6.83/2.49  tff(c_5635, plain, (![A_755, B_756, C_757]: (r2_hidden(k4_tarski('#skF_2'(A_755, B_756, C_757), A_755), C_757) | ~r2_hidden(A_755, k9_relat_1(C_757, B_756)) | ~v1_relat_1(C_757))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.83/2.49  tff(c_5716, plain, (![C_761, A_762, B_763]: (~v1_xboole_0(C_761) | ~r2_hidden(A_762, k9_relat_1(C_761, B_763)) | ~v1_relat_1(C_761))), inference(resolution, [status(thm)], [c_5635, c_2])).
% 6.83/2.49  tff(c_5723, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5582, c_5716])).
% 6.83/2.49  tff(c_5740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_5337, c_5723])).
% 6.83/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.83/2.49  
% 6.83/2.49  Inference rules
% 6.83/2.49  ----------------------
% 6.83/2.49  #Ref     : 0
% 6.83/2.49  #Sup     : 1127
% 6.83/2.49  #Fact    : 0
% 6.83/2.49  #Define  : 0
% 6.83/2.49  #Split   : 24
% 6.83/2.49  #Chain   : 0
% 6.83/2.49  #Close   : 0
% 6.83/2.49  
% 6.83/2.49  Ordering : KBO
% 6.83/2.49  
% 6.83/2.49  Simplification rules
% 6.83/2.49  ----------------------
% 6.83/2.49  #Subsume      : 227
% 6.83/2.49  #Demod        : 307
% 6.83/2.49  #Tautology    : 88
% 6.83/2.49  #SimpNegUnit  : 121
% 6.83/2.49  #BackRed      : 13
% 6.83/2.49  
% 6.83/2.49  #Partial instantiations: 0
% 6.83/2.49  #Strategies tried      : 1
% 6.83/2.49  
% 6.83/2.49  Timing (in seconds)
% 6.83/2.49  ----------------------
% 7.08/2.50  Preprocessing        : 0.34
% 7.08/2.50  Parsing              : 0.18
% 7.08/2.50  CNF conversion       : 0.03
% 7.08/2.50  Main loop            : 1.33
% 7.08/2.50  Inferencing          : 0.45
% 7.08/2.50  Reduction            : 0.37
% 7.08/2.50  Demodulation         : 0.23
% 7.08/2.50  BG Simplification    : 0.05
% 7.08/2.50  Subsumption          : 0.37
% 7.08/2.50  Abstraction          : 0.06
% 7.08/2.50  MUC search           : 0.00
% 7.08/2.50  Cooper               : 0.00
% 7.08/2.50  Total                : 1.72
% 7.08/2.50  Index Insertion      : 0.00
% 7.08/2.50  Index Deletion       : 0.00
% 7.08/2.50  Index Matching       : 0.00
% 7.08/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
