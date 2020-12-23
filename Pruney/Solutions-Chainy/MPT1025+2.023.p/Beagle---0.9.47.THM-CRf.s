%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 447 expanded)
%              Number of leaves         :   35 ( 166 expanded)
%              Depth                    :   10
%              Number of atoms          :  256 (1227 expanded)
%              Number of equality atoms :   23 ( 152 expanded)
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
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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

tff(c_209,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_hidden('#skF_2'(A_178,B_179,C_180),B_179)
      | ~ r2_hidden(A_178,k9_relat_1(C_180,B_179))
      | ~ v1_relat_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [B_184,A_185,C_186] :
      ( ~ v1_xboole_0(B_184)
      | ~ r2_hidden(A_185,k9_relat_1(C_186,B_184))
      | ~ v1_relat_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_249,plain,(
    ! [B_184,C_186] :
      ( ~ v1_xboole_0(B_184)
      | ~ v1_relat_1(C_186)
      | v1_xboole_0(k9_relat_1(C_186,B_184)) ) ),
    inference(resolution,[status(thm)],[c_4,c_234])).

tff(c_316,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k7_relset_1(A_205,B_206,C_207,D_208) = k9_relat_1(C_207,D_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_333,plain,(
    ! [D_208] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_208) = k9_relat_1('#skF_7',D_208) ),
    inference(resolution,[status(thm)],[c_50,c_316])).

tff(c_48,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_75,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_344,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_75])).

tff(c_362,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_249,c_344])).

tff(c_365,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_362])).

tff(c_345,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_48])).

tff(c_346,plain,(
    ! [D_212] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_212) = k9_relat_1('#skF_7',D_212) ),
    inference(resolution,[status(thm)],[c_50,c_316])).

tff(c_34,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( m1_subset_1(k7_relset_1(A_33,B_34,C_35,D_36),k1_zfmisc_1(B_34))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_352,plain,(
    ! [D_212] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_212),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_34])).

tff(c_392,plain,(
    ! [D_213] : m1_subset_1(k9_relat_1('#skF_7',D_213),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_352])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_400,plain,(
    ! [A_214,D_215] :
      ( m1_subset_1(A_214,'#skF_5')
      | ~ r2_hidden(A_214,k9_relat_1('#skF_7',D_215)) ) ),
    inference(resolution,[status(thm)],[c_392,c_12])).

tff(c_416,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_345,c_400])).

tff(c_146,plain,(
    ! [C_166,B_167,A_168] :
      ( v1_xboole_0(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(B_167,A_168)))
      | ~ v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_146])).

tff(c_158,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_157])).

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

tff(c_772,plain,(
    ! [C_255,A_256,D_259,B_258,E_257] :
      ( r2_hidden('#skF_3'(C_255,A_256,E_257,B_258,D_259),B_258)
      | ~ r2_hidden(E_257,k7_relset_1(C_255,A_256,D_259,B_258))
      | ~ m1_subset_1(E_257,A_256)
      | ~ m1_subset_1(D_259,k1_zfmisc_1(k2_zfmisc_1(C_255,A_256)))
      | v1_xboole_0(C_255)
      | v1_xboole_0(B_258)
      | v1_xboole_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_783,plain,(
    ! [E_257,B_258] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',E_257,B_258,'#skF_7'),B_258)
      | ~ r2_hidden(E_257,k7_relset_1('#skF_4','#skF_5','#skF_7',B_258))
      | ~ m1_subset_1(E_257,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_258)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_772])).

tff(c_790,plain,(
    ! [E_257,B_258] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',E_257,B_258,'#skF_7'),B_258)
      | ~ r2_hidden(E_257,k9_relat_1('#skF_7',B_258))
      | ~ m1_subset_1(E_257,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_258)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_783])).

tff(c_1871,plain,(
    ! [E_420,B_421] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',E_420,B_421,'#skF_7'),B_421)
      | ~ r2_hidden(E_420,k9_relat_1('#skF_7',B_421))
      | ~ m1_subset_1(E_420,'#skF_5')
      | v1_xboole_0(B_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_120,c_790])).

tff(c_46,plain,(
    ! [F_139] :
      ( k1_funct_1('#skF_7',F_139) != '#skF_8'
      | ~ r2_hidden(F_139,'#skF_6')
      | ~ m1_subset_1(F_139,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1974,plain,(
    ! [E_420] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_420,'#skF_6','#skF_7')) != '#skF_8'
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',E_420,'#skF_6','#skF_7'),'#skF_4')
      | ~ r2_hidden(E_420,k9_relat_1('#skF_7','#skF_6'))
      | ~ m1_subset_1(E_420,'#skF_5')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1871,c_46])).

tff(c_2054,plain,(
    ! [E_425] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_425,'#skF_6','#skF_7')) != '#skF_8'
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',E_425,'#skF_6','#skF_7'),'#skF_4')
      | ~ r2_hidden(E_425,k9_relat_1('#skF_7','#skF_6'))
      | ~ m1_subset_1(E_425,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_1974])).

tff(c_2073,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_345,c_2054])).

tff(c_2094,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_2073])).

tff(c_2103,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2094])).

tff(c_965,plain,(
    ! [A_285,C_284,E_286,D_288,B_287] :
      ( m1_subset_1('#skF_3'(C_284,A_285,E_286,B_287,D_288),C_284)
      | ~ r2_hidden(E_286,k7_relset_1(C_284,A_285,D_288,B_287))
      | ~ m1_subset_1(E_286,A_285)
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1(C_284,A_285)))
      | v1_xboole_0(C_284)
      | v1_xboole_0(B_287)
      | v1_xboole_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_973,plain,(
    ! [E_286,D_208] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_286,D_208,'#skF_7'),'#skF_4')
      | ~ r2_hidden(E_286,k9_relat_1('#skF_7',D_208))
      | ~ m1_subset_1(E_286,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_208)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_965])).

tff(c_986,plain,(
    ! [E_286,D_208] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_286,D_208,'#skF_7'),'#skF_4')
      | ~ r2_hidden(E_286,k9_relat_1('#skF_7',D_208))
      | ~ m1_subset_1(E_286,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_208)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_973])).

tff(c_2208,plain,(
    ! [E_438,D_439] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',E_438,D_439,'#skF_7'),'#skF_4')
      | ~ r2_hidden(E_438,k9_relat_1('#skF_7',D_439))
      | ~ m1_subset_1(E_438,'#skF_5')
      | v1_xboole_0(D_439) ) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_120,c_986])).

tff(c_2231,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_345,c_2208])).

tff(c_2254,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_2231])).

tff(c_2256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_2103,c_2254])).

tff(c_2257,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2094])).

tff(c_1131,plain,(
    ! [E_312,C_310,A_311,D_314,B_313] :
      ( r2_hidden(k4_tarski('#skF_3'(C_310,A_311,E_312,B_313,D_314),E_312),D_314)
      | ~ r2_hidden(E_312,k7_relset_1(C_310,A_311,D_314,B_313))
      | ~ m1_subset_1(E_312,A_311)
      | ~ m1_subset_1(D_314,k1_zfmisc_1(k2_zfmisc_1(C_310,A_311)))
      | v1_xboole_0(C_310)
      | v1_xboole_0(B_313)
      | v1_xboole_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5488,plain,(
    ! [C_651,A_649,B_652,E_653,D_650] :
      ( k1_funct_1(D_650,'#skF_3'(C_651,A_649,E_653,B_652,D_650)) = E_653
      | ~ v1_funct_1(D_650)
      | ~ v1_relat_1(D_650)
      | ~ r2_hidden(E_653,k7_relset_1(C_651,A_649,D_650,B_652))
      | ~ m1_subset_1(E_653,A_649)
      | ~ m1_subset_1(D_650,k1_zfmisc_1(k2_zfmisc_1(C_651,A_649)))
      | v1_xboole_0(C_651)
      | v1_xboole_0(B_652)
      | v1_xboole_0(A_649) ) ),
    inference(resolution,[status(thm)],[c_1131,c_24])).

tff(c_5504,plain,(
    ! [E_653,D_208] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_653,D_208,'#skF_7')) = E_653
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_653,k9_relat_1('#skF_7',D_208))
      | ~ m1_subset_1(E_653,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_208)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_5488])).

tff(c_5521,plain,(
    ! [E_653,D_208] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_653,D_208,'#skF_7')) = E_653
      | ~ r2_hidden(E_653,k9_relat_1('#skF_7',D_208))
      | ~ m1_subset_1(E_653,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_208)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_107,c_54,c_5504])).

tff(c_5559,plain,(
    ! [E_654,D_655] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5',E_654,D_655,'#skF_7')) = E_654
      | ~ r2_hidden(E_654,k9_relat_1('#skF_7',D_655))
      | ~ m1_subset_1(E_654,'#skF_5')
      | v1_xboole_0(D_655) ) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_120,c_5521])).

tff(c_5608,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_345,c_5559])).

tff(c_5656,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_5608])).

tff(c_5658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_2257,c_5656])).

tff(c_5659,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_5970,plain,(
    ! [A_713,C_714] :
      ( r2_hidden(k4_tarski(A_713,k1_funct_1(C_714,A_713)),C_714)
      | ~ r2_hidden(A_713,k1_relat_1(C_714))
      | ~ v1_funct_1(C_714)
      | ~ v1_relat_1(C_714) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6027,plain,(
    ! [C_715,A_716] :
      ( ~ v1_xboole_0(C_715)
      | ~ r2_hidden(A_716,k1_relat_1(C_715))
      | ~ v1_funct_1(C_715)
      | ~ v1_relat_1(C_715) ) ),
    inference(resolution,[status(thm)],[c_5970,c_2])).

tff(c_6052,plain,(
    ! [C_717] :
      ( ~ v1_xboole_0(C_717)
      | ~ v1_funct_1(C_717)
      | ~ v1_relat_1(C_717)
      | v1_xboole_0(k1_relat_1(C_717)) ) ),
    inference(resolution,[status(thm)],[c_4,c_6027])).

tff(c_5818,plain,(
    ! [A_692,B_693,C_694,D_695] :
      ( k7_relset_1(A_692,B_693,C_694,D_695) = k9_relat_1(C_694,D_695)
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(A_692,B_693))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5835,plain,(
    ! [D_695] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_695) = k9_relat_1('#skF_7',D_695) ),
    inference(resolution,[status(thm)],[c_50,c_5818])).

tff(c_5838,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5835,c_48])).

tff(c_5889,plain,(
    ! [A_698,B_699,C_700] :
      ( r2_hidden('#skF_2'(A_698,B_699,C_700),k1_relat_1(C_700))
      | ~ r2_hidden(A_698,k9_relat_1(C_700,B_699))
      | ~ v1_relat_1(C_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5923,plain,(
    ! [C_705,A_706,B_707] :
      ( ~ v1_xboole_0(k1_relat_1(C_705))
      | ~ r2_hidden(A_706,k9_relat_1(C_705,B_707))
      | ~ v1_relat_1(C_705) ) ),
    inference(resolution,[status(thm)],[c_5889,c_2])).

tff(c_5926,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5838,c_5923])).

tff(c_5941,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_5926])).

tff(c_6055,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6052,c_5941])).

tff(c_6059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_54,c_5659,c_6055])).

tff(c_6060,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_6257,plain,(
    ! [A_767,B_768,C_769,D_770] :
      ( k7_relset_1(A_767,B_768,C_769,D_770) = k9_relat_1(C_769,D_770)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6274,plain,(
    ! [D_770] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_770) = k9_relat_1('#skF_7',D_770) ),
    inference(resolution,[status(thm)],[c_50,c_6257])).

tff(c_6286,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_48])).

tff(c_6361,plain,(
    ! [A_778,B_779,C_780] :
      ( r2_hidden(k4_tarski('#skF_2'(A_778,B_779,C_780),A_778),C_780)
      | ~ r2_hidden(A_778,k9_relat_1(C_780,B_779))
      | ~ v1_relat_1(C_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6412,plain,(
    ! [C_781,A_782,B_783] :
      ( ~ v1_xboole_0(C_781)
      | ~ r2_hidden(A_782,k9_relat_1(C_781,B_783))
      | ~ v1_relat_1(C_781) ) ),
    inference(resolution,[status(thm)],[c_6361,c_2])).

tff(c_6419,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6286,c_6412])).

tff(c_6436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6060,c_6419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:37:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.57  
% 7.38/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.57  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 7.38/2.57  
% 7.38/2.57  %Foreground sorts:
% 7.38/2.57  
% 7.38/2.57  
% 7.38/2.57  %Background operators:
% 7.38/2.57  
% 7.38/2.57  
% 7.38/2.57  %Foreground operators:
% 7.38/2.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.38/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.38/2.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.38/2.57  tff('#skF_7', type, '#skF_7': $i).
% 7.38/2.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.38/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.38/2.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.38/2.57  tff('#skF_6', type, '#skF_6': $i).
% 7.38/2.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.38/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.38/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.38/2.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.38/2.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.38/2.57  tff('#skF_8', type, '#skF_8': $i).
% 7.38/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.38/2.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.38/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.38/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.38/2.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.38/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.38/2.57  
% 7.38/2.59  tff(f_142, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 7.38/2.59  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.38/2.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.38/2.59  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 7.38/2.59  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.38/2.59  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 7.38/2.59  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.38/2.59  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.38/2.59  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.38/2.59  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 7.38/2.59  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.38/2.59  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.38/2.59  tff(c_96, plain, (![C_150, A_151, B_152]: (v1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.38/2.59  tff(c_107, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_96])).
% 7.38/2.59  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.38/2.59  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.38/2.59  tff(c_209, plain, (![A_178, B_179, C_180]: (r2_hidden('#skF_2'(A_178, B_179, C_180), B_179) | ~r2_hidden(A_178, k9_relat_1(C_180, B_179)) | ~v1_relat_1(C_180))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.38/2.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.38/2.59  tff(c_234, plain, (![B_184, A_185, C_186]: (~v1_xboole_0(B_184) | ~r2_hidden(A_185, k9_relat_1(C_186, B_184)) | ~v1_relat_1(C_186))), inference(resolution, [status(thm)], [c_209, c_2])).
% 7.38/2.59  tff(c_249, plain, (![B_184, C_186]: (~v1_xboole_0(B_184) | ~v1_relat_1(C_186) | v1_xboole_0(k9_relat_1(C_186, B_184)))), inference(resolution, [status(thm)], [c_4, c_234])).
% 7.38/2.59  tff(c_316, plain, (![A_205, B_206, C_207, D_208]: (k7_relset_1(A_205, B_206, C_207, D_208)=k9_relat_1(C_207, D_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.38/2.59  tff(c_333, plain, (![D_208]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_208)=k9_relat_1('#skF_7', D_208))), inference(resolution, [status(thm)], [c_50, c_316])).
% 7.38/2.59  tff(c_48, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.38/2.59  tff(c_75, plain, (~v1_xboole_0(k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 7.38/2.59  tff(c_344, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_75])).
% 7.38/2.59  tff(c_362, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_249, c_344])).
% 7.38/2.59  tff(c_365, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_362])).
% 7.38/2.59  tff(c_345, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_48])).
% 7.38/2.59  tff(c_346, plain, (![D_212]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_212)=k9_relat_1('#skF_7', D_212))), inference(resolution, [status(thm)], [c_50, c_316])).
% 7.38/2.59  tff(c_34, plain, (![A_33, B_34, C_35, D_36]: (m1_subset_1(k7_relset_1(A_33, B_34, C_35, D_36), k1_zfmisc_1(B_34)) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.38/2.59  tff(c_352, plain, (![D_212]: (m1_subset_1(k9_relat_1('#skF_7', D_212), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_346, c_34])).
% 7.38/2.59  tff(c_392, plain, (![D_213]: (m1_subset_1(k9_relat_1('#skF_7', D_213), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_352])).
% 7.38/2.59  tff(c_12, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.38/2.59  tff(c_400, plain, (![A_214, D_215]: (m1_subset_1(A_214, '#skF_5') | ~r2_hidden(A_214, k9_relat_1('#skF_7', D_215)))), inference(resolution, [status(thm)], [c_392, c_12])).
% 7.38/2.59  tff(c_416, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_345, c_400])).
% 7.38/2.59  tff(c_146, plain, (![C_166, B_167, A_168]: (v1_xboole_0(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(B_167, A_168))) | ~v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.38/2.59  tff(c_157, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_146])).
% 7.38/2.59  tff(c_158, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_157])).
% 7.38/2.59  tff(c_108, plain, (![C_153, A_154, B_155]: (v1_xboole_0(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.38/2.59  tff(c_119, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_108])).
% 7.38/2.59  tff(c_120, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_119])).
% 7.38/2.59  tff(c_772, plain, (![C_255, A_256, D_259, B_258, E_257]: (r2_hidden('#skF_3'(C_255, A_256, E_257, B_258, D_259), B_258) | ~r2_hidden(E_257, k7_relset_1(C_255, A_256, D_259, B_258)) | ~m1_subset_1(E_257, A_256) | ~m1_subset_1(D_259, k1_zfmisc_1(k2_zfmisc_1(C_255, A_256))) | v1_xboole_0(C_255) | v1_xboole_0(B_258) | v1_xboole_0(A_256))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.38/2.59  tff(c_783, plain, (![E_257, B_258]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', E_257, B_258, '#skF_7'), B_258) | ~r2_hidden(E_257, k7_relset_1('#skF_4', '#skF_5', '#skF_7', B_258)) | ~m1_subset_1(E_257, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_258) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_772])).
% 7.38/2.59  tff(c_790, plain, (![E_257, B_258]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', E_257, B_258, '#skF_7'), B_258) | ~r2_hidden(E_257, k9_relat_1('#skF_7', B_258)) | ~m1_subset_1(E_257, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_258) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_783])).
% 7.38/2.59  tff(c_1871, plain, (![E_420, B_421]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', E_420, B_421, '#skF_7'), B_421) | ~r2_hidden(E_420, k9_relat_1('#skF_7', B_421)) | ~m1_subset_1(E_420, '#skF_5') | v1_xboole_0(B_421))), inference(negUnitSimplification, [status(thm)], [c_158, c_120, c_790])).
% 7.38/2.59  tff(c_46, plain, (![F_139]: (k1_funct_1('#skF_7', F_139)!='#skF_8' | ~r2_hidden(F_139, '#skF_6') | ~m1_subset_1(F_139, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.38/2.59  tff(c_1974, plain, (![E_420]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_420, '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_420, '#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden(E_420, k9_relat_1('#skF_7', '#skF_6')) | ~m1_subset_1(E_420, '#skF_5') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_1871, c_46])).
% 7.38/2.59  tff(c_2054, plain, (![E_425]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_425, '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_425, '#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden(E_425, k9_relat_1('#skF_7', '#skF_6')) | ~m1_subset_1(E_425, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_365, c_1974])).
% 7.38/2.59  tff(c_2073, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_345, c_2054])).
% 7.38/2.59  tff(c_2094, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_2073])).
% 7.38/2.59  tff(c_2103, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2094])).
% 7.38/2.59  tff(c_965, plain, (![A_285, C_284, E_286, D_288, B_287]: (m1_subset_1('#skF_3'(C_284, A_285, E_286, B_287, D_288), C_284) | ~r2_hidden(E_286, k7_relset_1(C_284, A_285, D_288, B_287)) | ~m1_subset_1(E_286, A_285) | ~m1_subset_1(D_288, k1_zfmisc_1(k2_zfmisc_1(C_284, A_285))) | v1_xboole_0(C_284) | v1_xboole_0(B_287) | v1_xboole_0(A_285))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.38/2.59  tff(c_973, plain, (![E_286, D_208]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_286, D_208, '#skF_7'), '#skF_4') | ~r2_hidden(E_286, k9_relat_1('#skF_7', D_208)) | ~m1_subset_1(E_286, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_208) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_965])).
% 7.38/2.59  tff(c_986, plain, (![E_286, D_208]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_286, D_208, '#skF_7'), '#skF_4') | ~r2_hidden(E_286, k9_relat_1('#skF_7', D_208)) | ~m1_subset_1(E_286, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_208) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_973])).
% 7.38/2.59  tff(c_2208, plain, (![E_438, D_439]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', E_438, D_439, '#skF_7'), '#skF_4') | ~r2_hidden(E_438, k9_relat_1('#skF_7', D_439)) | ~m1_subset_1(E_438, '#skF_5') | v1_xboole_0(D_439))), inference(negUnitSimplification, [status(thm)], [c_158, c_120, c_986])).
% 7.38/2.59  tff(c_2231, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_345, c_2208])).
% 7.38/2.59  tff(c_2254, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'), '#skF_4') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_2231])).
% 7.38/2.59  tff(c_2256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_365, c_2103, c_2254])).
% 7.38/2.59  tff(c_2257, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(splitRight, [status(thm)], [c_2094])).
% 7.38/2.59  tff(c_1131, plain, (![E_312, C_310, A_311, D_314, B_313]: (r2_hidden(k4_tarski('#skF_3'(C_310, A_311, E_312, B_313, D_314), E_312), D_314) | ~r2_hidden(E_312, k7_relset_1(C_310, A_311, D_314, B_313)) | ~m1_subset_1(E_312, A_311) | ~m1_subset_1(D_314, k1_zfmisc_1(k2_zfmisc_1(C_310, A_311))) | v1_xboole_0(C_310) | v1_xboole_0(B_313) | v1_xboole_0(A_311))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.38/2.59  tff(c_24, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.38/2.59  tff(c_5488, plain, (![C_651, A_649, B_652, E_653, D_650]: (k1_funct_1(D_650, '#skF_3'(C_651, A_649, E_653, B_652, D_650))=E_653 | ~v1_funct_1(D_650) | ~v1_relat_1(D_650) | ~r2_hidden(E_653, k7_relset_1(C_651, A_649, D_650, B_652)) | ~m1_subset_1(E_653, A_649) | ~m1_subset_1(D_650, k1_zfmisc_1(k2_zfmisc_1(C_651, A_649))) | v1_xboole_0(C_651) | v1_xboole_0(B_652) | v1_xboole_0(A_649))), inference(resolution, [status(thm)], [c_1131, c_24])).
% 7.38/2.59  tff(c_5504, plain, (![E_653, D_208]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_653, D_208, '#skF_7'))=E_653 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(E_653, k9_relat_1('#skF_7', D_208)) | ~m1_subset_1(E_653, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_208) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_5488])).
% 7.38/2.59  tff(c_5521, plain, (![E_653, D_208]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_653, D_208, '#skF_7'))=E_653 | ~r2_hidden(E_653, k9_relat_1('#skF_7', D_208)) | ~m1_subset_1(E_653, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_208) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_107, c_54, c_5504])).
% 7.38/2.59  tff(c_5559, plain, (![E_654, D_655]: (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', E_654, D_655, '#skF_7'))=E_654 | ~r2_hidden(E_654, k9_relat_1('#skF_7', D_655)) | ~m1_subset_1(E_654, '#skF_5') | v1_xboole_0(D_655))), inference(negUnitSimplification, [status(thm)], [c_158, c_120, c_5521])).
% 7.38/2.59  tff(c_5608, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_345, c_5559])).
% 7.38/2.59  tff(c_5656, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_8', '#skF_6', '#skF_7'))='#skF_8' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_5608])).
% 7.38/2.59  tff(c_5658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_365, c_2257, c_5656])).
% 7.38/2.59  tff(c_5659, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_157])).
% 7.38/2.59  tff(c_5970, plain, (![A_713, C_714]: (r2_hidden(k4_tarski(A_713, k1_funct_1(C_714, A_713)), C_714) | ~r2_hidden(A_713, k1_relat_1(C_714)) | ~v1_funct_1(C_714) | ~v1_relat_1(C_714))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.38/2.59  tff(c_6027, plain, (![C_715, A_716]: (~v1_xboole_0(C_715) | ~r2_hidden(A_716, k1_relat_1(C_715)) | ~v1_funct_1(C_715) | ~v1_relat_1(C_715))), inference(resolution, [status(thm)], [c_5970, c_2])).
% 7.38/2.59  tff(c_6052, plain, (![C_717]: (~v1_xboole_0(C_717) | ~v1_funct_1(C_717) | ~v1_relat_1(C_717) | v1_xboole_0(k1_relat_1(C_717)))), inference(resolution, [status(thm)], [c_4, c_6027])).
% 7.38/2.59  tff(c_5818, plain, (![A_692, B_693, C_694, D_695]: (k7_relset_1(A_692, B_693, C_694, D_695)=k9_relat_1(C_694, D_695) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(A_692, B_693))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.38/2.59  tff(c_5835, plain, (![D_695]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_695)=k9_relat_1('#skF_7', D_695))), inference(resolution, [status(thm)], [c_50, c_5818])).
% 7.38/2.59  tff(c_5838, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5835, c_48])).
% 7.38/2.59  tff(c_5889, plain, (![A_698, B_699, C_700]: (r2_hidden('#skF_2'(A_698, B_699, C_700), k1_relat_1(C_700)) | ~r2_hidden(A_698, k9_relat_1(C_700, B_699)) | ~v1_relat_1(C_700))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.38/2.59  tff(c_5923, plain, (![C_705, A_706, B_707]: (~v1_xboole_0(k1_relat_1(C_705)) | ~r2_hidden(A_706, k9_relat_1(C_705, B_707)) | ~v1_relat_1(C_705))), inference(resolution, [status(thm)], [c_5889, c_2])).
% 7.38/2.59  tff(c_5926, plain, (~v1_xboole_0(k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5838, c_5923])).
% 7.38/2.59  tff(c_5941, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_5926])).
% 7.38/2.59  tff(c_6055, plain, (~v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6052, c_5941])).
% 7.38/2.59  tff(c_6059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_54, c_5659, c_6055])).
% 7.38/2.59  tff(c_6060, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_119])).
% 7.38/2.59  tff(c_6257, plain, (![A_767, B_768, C_769, D_770]: (k7_relset_1(A_767, B_768, C_769, D_770)=k9_relat_1(C_769, D_770) | ~m1_subset_1(C_769, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.38/2.59  tff(c_6274, plain, (![D_770]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_770)=k9_relat_1('#skF_7', D_770))), inference(resolution, [status(thm)], [c_50, c_6257])).
% 7.38/2.59  tff(c_6286, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_48])).
% 7.38/2.59  tff(c_6361, plain, (![A_778, B_779, C_780]: (r2_hidden(k4_tarski('#skF_2'(A_778, B_779, C_780), A_778), C_780) | ~r2_hidden(A_778, k9_relat_1(C_780, B_779)) | ~v1_relat_1(C_780))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.38/2.59  tff(c_6412, plain, (![C_781, A_782, B_783]: (~v1_xboole_0(C_781) | ~r2_hidden(A_782, k9_relat_1(C_781, B_783)) | ~v1_relat_1(C_781))), inference(resolution, [status(thm)], [c_6361, c_2])).
% 7.38/2.59  tff(c_6419, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6286, c_6412])).
% 7.38/2.59  tff(c_6436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_6060, c_6419])).
% 7.38/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.59  
% 7.38/2.59  Inference rules
% 7.38/2.59  ----------------------
% 7.38/2.59  #Ref     : 0
% 7.38/2.59  #Sup     : 1285
% 7.38/2.59  #Fact    : 0
% 7.38/2.59  #Define  : 0
% 7.38/2.59  #Split   : 22
% 7.38/2.59  #Chain   : 0
% 7.38/2.59  #Close   : 0
% 7.38/2.59  
% 7.38/2.59  Ordering : KBO
% 7.38/2.59  
% 7.38/2.59  Simplification rules
% 7.38/2.59  ----------------------
% 7.38/2.59  #Subsume      : 292
% 7.38/2.59  #Demod        : 363
% 7.38/2.59  #Tautology    : 93
% 7.38/2.59  #SimpNegUnit  : 136
% 7.38/2.59  #BackRed      : 10
% 7.38/2.59  
% 7.38/2.59  #Partial instantiations: 0
% 7.38/2.59  #Strategies tried      : 1
% 7.38/2.59  
% 7.38/2.59  Timing (in seconds)
% 7.38/2.59  ----------------------
% 7.58/2.60  Preprocessing        : 0.35
% 7.58/2.60  Parsing              : 0.18
% 7.58/2.60  CNF conversion       : 0.03
% 7.58/2.60  Main loop            : 1.49
% 7.58/2.60  Inferencing          : 0.50
% 7.58/2.60  Reduction            : 0.39
% 7.58/2.60  Demodulation         : 0.26
% 7.58/2.60  BG Simplification    : 0.05
% 7.58/2.60  Subsumption          : 0.43
% 7.58/2.60  Abstraction          : 0.06
% 7.58/2.60  MUC search           : 0.00
% 7.58/2.60  Cooper               : 0.00
% 7.58/2.60  Total                : 1.89
% 7.58/2.60  Index Insertion      : 0.00
% 7.58/2.60  Index Deletion       : 0.00
% 7.58/2.60  Index Matching       : 0.00
% 7.58/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
