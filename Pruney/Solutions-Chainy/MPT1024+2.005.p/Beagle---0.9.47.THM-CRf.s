%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:22 EST 2020

% Result     : Theorem 13.48s
% Output     : CNFRefutation 13.60s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 393 expanded)
%              Number of leaves         :   39 ( 148 expanded)
%              Depth                    :   10
%              Number of atoms          :  289 (1055 expanded)
%              Number of equality atoms :   22 ( 117 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_132,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_75,plain,(
    ! [C_148,A_149,B_150] :
      ( v1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_84,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_195,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden('#skF_3'(A_171,B_172,C_173),B_172)
      | ~ r2_hidden(A_171,k9_relat_1(C_173,B_172))
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [B_174,A_175,C_176] :
      ( ~ v1_xboole_0(B_174)
      | ~ r2_hidden(A_175,k9_relat_1(C_176,B_174))
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_230,plain,(
    ! [B_174,C_176] :
      ( ~ v1_xboole_0(B_174)
      | ~ v1_relat_1(C_176)
      | v1_xboole_0(k9_relat_1(C_176,B_174)) ) ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_361,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( k7_relset_1(A_219,B_220,C_221,D_222) = k9_relat_1(C_221,D_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_376,plain,(
    ! [D_222] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_222) = k9_relat_1('#skF_8',D_222) ),
    inference(resolution,[status(thm)],[c_52,c_361])).

tff(c_50,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_68,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_377,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_68])).

tff(c_398,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_230,c_377])).

tff(c_404,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_398])).

tff(c_378,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_50])).

tff(c_379,plain,(
    ! [D_223] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_223) = k9_relat_1('#skF_8',D_223) ),
    inference(resolution,[status(thm)],[c_52,c_361])).

tff(c_36,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( m1_subset_1(k7_relset_1(A_35,B_36,C_37,D_38),k1_zfmisc_1(B_36))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_385,plain,(
    ! [D_223] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_223),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_36])).

tff(c_421,plain,(
    ! [D_224] : m1_subset_1(k9_relat_1('#skF_8',D_224),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_385])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_429,plain,(
    ! [A_225,D_226] :
      ( m1_subset_1(A_225,'#skF_6')
      | ~ r2_hidden(A_225,k9_relat_1('#skF_8',D_226)) ) ),
    inference(resolution,[status(thm)],[c_421,c_14])).

tff(c_445,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_378,c_429])).

tff(c_106,plain,(
    ! [C_157,B_158,A_159] :
      ( v1_xboole_0(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(B_158,A_159)))
      | ~ v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_115,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_106])).

tff(c_116,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_123,plain,(
    ! [C_160,A_161,B_162] :
      ( v1_xboole_0(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_123])).

tff(c_140,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_1031,plain,(
    ! [A_308,D_307,E_306,B_305,C_309] :
      ( m1_subset_1('#skF_4'(B_305,E_306,D_307,A_308,C_309),C_309)
      | ~ r2_hidden(E_306,k7_relset_1(C_309,A_308,D_307,B_305))
      | ~ m1_subset_1(E_306,A_308)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(C_309,A_308)))
      | v1_xboole_0(C_309)
      | v1_xboole_0(B_305)
      | v1_xboole_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1039,plain,(
    ! [D_222,E_306] :
      ( m1_subset_1('#skF_4'(D_222,E_306,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_306,k9_relat_1('#skF_8',D_222))
      | ~ m1_subset_1(E_306,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_222)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_1031])).

tff(c_1052,plain,(
    ! [D_222,E_306] :
      ( m1_subset_1('#skF_4'(D_222,E_306,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_306,k9_relat_1('#skF_8',D_222))
      | ~ m1_subset_1(E_306,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_222)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1039])).

tff(c_1797,plain,(
    ! [D_386,E_387] :
      ( m1_subset_1('#skF_4'(D_386,E_387,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_387,k9_relat_1('#skF_8',D_386))
      | ~ m1_subset_1(E_387,'#skF_6')
      | v1_xboole_0(D_386) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_140,c_1052])).

tff(c_1820,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_378,c_1797])).

tff(c_1843,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_1820])).

tff(c_1844,plain,(
    m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_1843])).

tff(c_1327,plain,(
    ! [D_335,C_337,A_336,E_334,B_333] :
      ( r2_hidden(k4_tarski('#skF_4'(B_333,E_334,D_335,A_336,C_337),E_334),D_335)
      | ~ r2_hidden(E_334,k7_relset_1(C_337,A_336,D_335,B_333))
      | ~ m1_subset_1(E_334,A_336)
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(C_337,A_336)))
      | v1_xboole_0(C_337)
      | v1_xboole_0(B_333)
      | v1_xboole_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6277,plain,(
    ! [E_687,B_690,C_691,D_689,A_688] :
      ( k1_funct_1(D_689,'#skF_4'(B_690,E_687,D_689,A_688,C_691)) = E_687
      | ~ v1_funct_1(D_689)
      | ~ v1_relat_1(D_689)
      | ~ r2_hidden(E_687,k7_relset_1(C_691,A_688,D_689,B_690))
      | ~ m1_subset_1(E_687,A_688)
      | ~ m1_subset_1(D_689,k1_zfmisc_1(k2_zfmisc_1(C_691,A_688)))
      | v1_xboole_0(C_691)
      | v1_xboole_0(B_690)
      | v1_xboole_0(A_688) ) ),
    inference(resolution,[status(thm)],[c_1327,c_26])).

tff(c_6296,plain,(
    ! [D_222,E_687] :
      ( k1_funct_1('#skF_8','#skF_4'(D_222,E_687,'#skF_8','#skF_6','#skF_5')) = E_687
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(E_687,k9_relat_1('#skF_8',D_222))
      | ~ m1_subset_1(E_687,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_222)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_6277])).

tff(c_6312,plain,(
    ! [D_222,E_687] :
      ( k1_funct_1('#skF_8','#skF_4'(D_222,E_687,'#skF_8','#skF_6','#skF_5')) = E_687
      | ~ r2_hidden(E_687,k9_relat_1('#skF_8',D_222))
      | ~ m1_subset_1(E_687,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_222)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_56,c_6296])).

tff(c_6317,plain,(
    ! [D_692,E_693] :
      ( k1_funct_1('#skF_8','#skF_4'(D_692,E_693,'#skF_8','#skF_6','#skF_5')) = E_693
      | ~ r2_hidden(E_693,k9_relat_1('#skF_8',D_692))
      | ~ m1_subset_1(E_693,'#skF_6')
      | v1_xboole_0(D_692) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_140,c_6312])).

tff(c_6374,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) = '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_378,c_6317])).

tff(c_6427,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) = '#skF_9'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_6374])).

tff(c_6428,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_6427])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_894,plain,(
    ! [A_282,B_279,D_281,C_283,E_280] :
      ( r2_hidden('#skF_4'(B_279,E_280,D_281,A_282,C_283),B_279)
      | ~ r2_hidden(E_280,k7_relset_1(C_283,A_282,D_281,B_279))
      | ~ m1_subset_1(E_280,A_282)
      | ~ m1_subset_1(D_281,k1_zfmisc_1(k2_zfmisc_1(C_283,A_282)))
      | v1_xboole_0(C_283)
      | v1_xboole_0(B_279)
      | v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_905,plain,(
    ! [B_279,E_280] :
      ( r2_hidden('#skF_4'(B_279,E_280,'#skF_8','#skF_6','#skF_5'),B_279)
      | ~ r2_hidden(E_280,k7_relset_1('#skF_5','#skF_6','#skF_8',B_279))
      | ~ m1_subset_1(E_280,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_279)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_894])).

tff(c_910,plain,(
    ! [B_279,E_280] :
      ( r2_hidden('#skF_4'(B_279,E_280,'#skF_8','#skF_6','#skF_5'),B_279)
      | ~ r2_hidden(E_280,k9_relat_1('#skF_8',B_279))
      | ~ m1_subset_1(E_280,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_279)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_905])).

tff(c_1147,plain,(
    ! [B_318,E_319] :
      ( r2_hidden('#skF_4'(B_318,E_319,'#skF_8','#skF_6','#skF_5'),B_318)
      | ~ r2_hidden(E_319,k9_relat_1('#skF_8',B_318))
      | ~ m1_subset_1(E_319,'#skF_6')
      | v1_xboole_0(B_318) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_140,c_910])).

tff(c_48,plain,(
    ! [F_141] :
      ( k1_funct_1('#skF_8',F_141) != '#skF_9'
      | ~ r2_hidden(F_141,'#skF_7')
      | ~ r2_hidden(F_141,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1220,plain,(
    ! [E_319] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_7',E_319,'#skF_8','#skF_6','#skF_5')) != '#skF_9'
      | ~ r2_hidden('#skF_4'('#skF_7',E_319,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_319,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_319,'#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1147,c_48])).

tff(c_1629,plain,(
    ! [E_358] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_7',E_358,'#skF_8','#skF_6','#skF_5')) != '#skF_9'
      | ~ r2_hidden('#skF_4'('#skF_7',E_358,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_358,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_358,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_1220])).

tff(c_1632,plain,(
    ! [E_358] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_7',E_358,'#skF_8','#skF_6','#skF_5')) != '#skF_9'
      | ~ r2_hidden(E_358,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_358,'#skF_6')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_4'('#skF_7',E_358,'#skF_8','#skF_6','#skF_5'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_1629])).

tff(c_9297,plain,(
    ! [E_814] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_7',E_814,'#skF_8','#skF_6','#skF_5')) != '#skF_9'
      | ~ r2_hidden(E_814,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_814,'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_7',E_814,'#skF_8','#skF_6','#skF_5'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_1632])).

tff(c_9348,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) != '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_378,c_9297])).

tff(c_9400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_445,c_6428,c_9348])).

tff(c_9402,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_8,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5),k1_zfmisc_1(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9446,plain,(
    ! [A_822,B_823] :
      ( v1_xboole_0('#skF_2'(k2_zfmisc_1(A_822,B_823)))
      | ~ v1_xboole_0(A_822)
      | v1_xboole_0(k2_zfmisc_1(A_822,B_823)) ) ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0('#skF_2'(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9451,plain,(
    ! [A_824,B_825] :
      ( ~ v1_xboole_0(A_824)
      | v1_xboole_0(k2_zfmisc_1(A_824,B_825)) ) ),
    inference(resolution,[status(thm)],[c_9446,c_6])).

tff(c_85,plain,(
    ! [B_151,A_152] :
      ( v1_xboole_0(B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_152))
      | ~ v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_85])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_9454,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_9451,c_94])).

tff(c_9458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9402,c_9454])).

tff(c_9460,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_9534,plain,(
    ! [B_837,A_838] :
      ( v1_xboole_0('#skF_2'(k2_zfmisc_1(B_837,A_838)))
      | ~ v1_xboole_0(A_838)
      | v1_xboole_0(k2_zfmisc_1(B_837,A_838)) ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_9539,plain,(
    ! [A_839,B_840] :
      ( ~ v1_xboole_0(A_839)
      | v1_xboole_0(k2_zfmisc_1(B_840,A_839)) ) ),
    inference(resolution,[status(thm)],[c_9534,c_6])).

tff(c_9542,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9539,c_94])).

tff(c_9546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9460,c_9542])).

tff(c_9547,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_9899,plain,(
    ! [A_916,C_917] :
      ( r2_hidden(k4_tarski(A_916,k1_funct_1(C_917,A_916)),C_917)
      | ~ r2_hidden(A_916,k1_relat_1(C_917))
      | ~ v1_funct_1(C_917)
      | ~ v1_relat_1(C_917) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9953,plain,(
    ! [C_918,A_919] :
      ( ~ v1_xboole_0(C_918)
      | ~ r2_hidden(A_919,k1_relat_1(C_918))
      | ~ v1_funct_1(C_918)
      | ~ v1_relat_1(C_918) ) ),
    inference(resolution,[status(thm)],[c_9899,c_2])).

tff(c_9978,plain,(
    ! [C_920] :
      ( ~ v1_xboole_0(C_920)
      | ~ v1_funct_1(C_920)
      | ~ v1_relat_1(C_920)
      | v1_xboole_0(k1_relat_1(C_920)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9953])).

tff(c_9740,plain,(
    ! [A_890,B_891,C_892] :
      ( r2_hidden('#skF_3'(A_890,B_891,C_892),k1_relat_1(C_892))
      | ~ r2_hidden(A_890,k9_relat_1(C_892,B_891))
      | ~ v1_relat_1(C_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9745,plain,(
    ! [C_893,A_894,B_895] :
      ( ~ v1_xboole_0(k1_relat_1(C_893))
      | ~ r2_hidden(A_894,k9_relat_1(C_893,B_895))
      | ~ v1_relat_1(C_893) ) ),
    inference(resolution,[status(thm)],[c_9740,c_2])).

tff(c_9760,plain,(
    ! [C_893,B_895] :
      ( ~ v1_xboole_0(k1_relat_1(C_893))
      | ~ v1_relat_1(C_893)
      | v1_xboole_0(k9_relat_1(C_893,B_895)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9745])).

tff(c_9764,plain,(
    ! [A_901,B_902,C_903,D_904] :
      ( k7_relset_1(A_901,B_902,C_903,D_904) = k9_relat_1(C_903,D_904)
      | ~ m1_subset_1(C_903,k1_zfmisc_1(k2_zfmisc_1(A_901,B_902))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_9775,plain,(
    ! [D_904] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_904) = k9_relat_1('#skF_8',D_904) ),
    inference(resolution,[status(thm)],[c_52,c_9764])).

tff(c_9776,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9775,c_68])).

tff(c_9789,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_9760,c_9776])).

tff(c_9795,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9789])).

tff(c_9981,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_9978,c_9795])).

tff(c_9985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_9547,c_9981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.48/5.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.60/5.50  
% 13.60/5.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.60/5.51  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 13.60/5.51  
% 13.60/5.51  %Foreground sorts:
% 13.60/5.51  
% 13.60/5.51  
% 13.60/5.51  %Background operators:
% 13.60/5.51  
% 13.60/5.51  
% 13.60/5.51  %Foreground operators:
% 13.60/5.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.60/5.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.60/5.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.60/5.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.60/5.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.60/5.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.60/5.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 13.60/5.51  tff('#skF_7', type, '#skF_7': $i).
% 13.60/5.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.60/5.51  tff('#skF_5', type, '#skF_5': $i).
% 13.60/5.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.60/5.51  tff('#skF_6', type, '#skF_6': $i).
% 13.60/5.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.60/5.51  tff('#skF_9', type, '#skF_9': $i).
% 13.60/5.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.60/5.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.60/5.51  tff('#skF_8', type, '#skF_8': $i).
% 13.60/5.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.60/5.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.60/5.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.60/5.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.60/5.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.60/5.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.60/5.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.60/5.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.60/5.51  
% 13.60/5.54  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 13.60/5.54  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.60/5.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.60/5.54  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 13.60/5.54  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.60/5.54  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 13.60/5.54  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 13.60/5.54  tff(f_98, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.60/5.54  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 13.60/5.54  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 13.60/5.54  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 13.60/5.54  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 13.60/5.54  tff(f_40, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 13.60/5.54  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 13.60/5.54  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 13.60/5.54  tff(c_75, plain, (![C_148, A_149, B_150]: (v1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.60/5.54  tff(c_84, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_75])).
% 13.60/5.54  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_151])).
% 13.60/5.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.60/5.54  tff(c_195, plain, (![A_171, B_172, C_173]: (r2_hidden('#skF_3'(A_171, B_172, C_173), B_172) | ~r2_hidden(A_171, k9_relat_1(C_173, B_172)) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.60/5.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.60/5.54  tff(c_215, plain, (![B_174, A_175, C_176]: (~v1_xboole_0(B_174) | ~r2_hidden(A_175, k9_relat_1(C_176, B_174)) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_195, c_2])).
% 13.60/5.54  tff(c_230, plain, (![B_174, C_176]: (~v1_xboole_0(B_174) | ~v1_relat_1(C_176) | v1_xboole_0(k9_relat_1(C_176, B_174)))), inference(resolution, [status(thm)], [c_4, c_215])).
% 13.60/5.54  tff(c_361, plain, (![A_219, B_220, C_221, D_222]: (k7_relset_1(A_219, B_220, C_221, D_222)=k9_relat_1(C_221, D_222) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.60/5.54  tff(c_376, plain, (![D_222]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_222)=k9_relat_1('#skF_8', D_222))), inference(resolution, [status(thm)], [c_52, c_361])).
% 13.60/5.54  tff(c_50, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 13.60/5.54  tff(c_68, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 13.60/5.54  tff(c_377, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_68])).
% 13.60/5.54  tff(c_398, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_230, c_377])).
% 13.60/5.54  tff(c_404, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_398])).
% 13.60/5.54  tff(c_378, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_50])).
% 13.60/5.54  tff(c_379, plain, (![D_223]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_223)=k9_relat_1('#skF_8', D_223))), inference(resolution, [status(thm)], [c_52, c_361])).
% 13.60/5.54  tff(c_36, plain, (![A_35, B_36, C_37, D_38]: (m1_subset_1(k7_relset_1(A_35, B_36, C_37, D_38), k1_zfmisc_1(B_36)) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.60/5.54  tff(c_385, plain, (![D_223]: (m1_subset_1(k9_relat_1('#skF_8', D_223), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_379, c_36])).
% 13.60/5.54  tff(c_421, plain, (![D_224]: (m1_subset_1(k9_relat_1('#skF_8', D_224), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_385])).
% 13.60/5.54  tff(c_14, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.60/5.54  tff(c_429, plain, (![A_225, D_226]: (m1_subset_1(A_225, '#skF_6') | ~r2_hidden(A_225, k9_relat_1('#skF_8', D_226)))), inference(resolution, [status(thm)], [c_421, c_14])).
% 13.60/5.54  tff(c_445, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_378, c_429])).
% 13.60/5.54  tff(c_106, plain, (![C_157, B_158, A_159]: (v1_xboole_0(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(B_158, A_159))) | ~v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.60/5.54  tff(c_115, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_106])).
% 13.60/5.54  tff(c_116, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_115])).
% 13.60/5.54  tff(c_123, plain, (![C_160, A_161, B_162]: (v1_xboole_0(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.60/5.54  tff(c_132, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_123])).
% 13.60/5.54  tff(c_140, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_132])).
% 13.60/5.54  tff(c_1031, plain, (![A_308, D_307, E_306, B_305, C_309]: (m1_subset_1('#skF_4'(B_305, E_306, D_307, A_308, C_309), C_309) | ~r2_hidden(E_306, k7_relset_1(C_309, A_308, D_307, B_305)) | ~m1_subset_1(E_306, A_308) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(C_309, A_308))) | v1_xboole_0(C_309) | v1_xboole_0(B_305) | v1_xboole_0(A_308))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.60/5.54  tff(c_1039, plain, (![D_222, E_306]: (m1_subset_1('#skF_4'(D_222, E_306, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_306, k9_relat_1('#skF_8', D_222)) | ~m1_subset_1(E_306, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_222) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_1031])).
% 13.60/5.54  tff(c_1052, plain, (![D_222, E_306]: (m1_subset_1('#skF_4'(D_222, E_306, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_306, k9_relat_1('#skF_8', D_222)) | ~m1_subset_1(E_306, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_222) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1039])).
% 13.60/5.54  tff(c_1797, plain, (![D_386, E_387]: (m1_subset_1('#skF_4'(D_386, E_387, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_387, k9_relat_1('#skF_8', D_386)) | ~m1_subset_1(E_387, '#skF_6') | v1_xboole_0(D_386))), inference(negUnitSimplification, [status(thm)], [c_116, c_140, c_1052])).
% 13.60/5.54  tff(c_1820, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_378, c_1797])).
% 13.60/5.54  tff(c_1843, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_1820])).
% 13.60/5.54  tff(c_1844, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_404, c_1843])).
% 13.60/5.54  tff(c_1327, plain, (![D_335, C_337, A_336, E_334, B_333]: (r2_hidden(k4_tarski('#skF_4'(B_333, E_334, D_335, A_336, C_337), E_334), D_335) | ~r2_hidden(E_334, k7_relset_1(C_337, A_336, D_335, B_333)) | ~m1_subset_1(E_334, A_336) | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(C_337, A_336))) | v1_xboole_0(C_337) | v1_xboole_0(B_333) | v1_xboole_0(A_336))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.60/5.54  tff(c_26, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.60/5.54  tff(c_6277, plain, (![E_687, B_690, C_691, D_689, A_688]: (k1_funct_1(D_689, '#skF_4'(B_690, E_687, D_689, A_688, C_691))=E_687 | ~v1_funct_1(D_689) | ~v1_relat_1(D_689) | ~r2_hidden(E_687, k7_relset_1(C_691, A_688, D_689, B_690)) | ~m1_subset_1(E_687, A_688) | ~m1_subset_1(D_689, k1_zfmisc_1(k2_zfmisc_1(C_691, A_688))) | v1_xboole_0(C_691) | v1_xboole_0(B_690) | v1_xboole_0(A_688))), inference(resolution, [status(thm)], [c_1327, c_26])).
% 13.60/5.54  tff(c_6296, plain, (![D_222, E_687]: (k1_funct_1('#skF_8', '#skF_4'(D_222, E_687, '#skF_8', '#skF_6', '#skF_5'))=E_687 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(E_687, k9_relat_1('#skF_8', D_222)) | ~m1_subset_1(E_687, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_222) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_6277])).
% 13.60/5.54  tff(c_6312, plain, (![D_222, E_687]: (k1_funct_1('#skF_8', '#skF_4'(D_222, E_687, '#skF_8', '#skF_6', '#skF_5'))=E_687 | ~r2_hidden(E_687, k9_relat_1('#skF_8', D_222)) | ~m1_subset_1(E_687, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_222) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_56, c_6296])).
% 13.60/5.54  tff(c_6317, plain, (![D_692, E_693]: (k1_funct_1('#skF_8', '#skF_4'(D_692, E_693, '#skF_8', '#skF_6', '#skF_5'))=E_693 | ~r2_hidden(E_693, k9_relat_1('#skF_8', D_692)) | ~m1_subset_1(E_693, '#skF_6') | v1_xboole_0(D_692))), inference(negUnitSimplification, [status(thm)], [c_116, c_140, c_6312])).
% 13.60/5.54  tff(c_6374, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_378, c_6317])).
% 13.60/5.54  tff(c_6427, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))='#skF_9' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_6374])).
% 13.60/5.54  tff(c_6428, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_404, c_6427])).
% 13.60/5.54  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.60/5.54  tff(c_894, plain, (![A_282, B_279, D_281, C_283, E_280]: (r2_hidden('#skF_4'(B_279, E_280, D_281, A_282, C_283), B_279) | ~r2_hidden(E_280, k7_relset_1(C_283, A_282, D_281, B_279)) | ~m1_subset_1(E_280, A_282) | ~m1_subset_1(D_281, k1_zfmisc_1(k2_zfmisc_1(C_283, A_282))) | v1_xboole_0(C_283) | v1_xboole_0(B_279) | v1_xboole_0(A_282))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.60/5.54  tff(c_905, plain, (![B_279, E_280]: (r2_hidden('#skF_4'(B_279, E_280, '#skF_8', '#skF_6', '#skF_5'), B_279) | ~r2_hidden(E_280, k7_relset_1('#skF_5', '#skF_6', '#skF_8', B_279)) | ~m1_subset_1(E_280, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_279) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_894])).
% 13.60/5.54  tff(c_910, plain, (![B_279, E_280]: (r2_hidden('#skF_4'(B_279, E_280, '#skF_8', '#skF_6', '#skF_5'), B_279) | ~r2_hidden(E_280, k9_relat_1('#skF_8', B_279)) | ~m1_subset_1(E_280, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_279) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_905])).
% 13.60/5.54  tff(c_1147, plain, (![B_318, E_319]: (r2_hidden('#skF_4'(B_318, E_319, '#skF_8', '#skF_6', '#skF_5'), B_318) | ~r2_hidden(E_319, k9_relat_1('#skF_8', B_318)) | ~m1_subset_1(E_319, '#skF_6') | v1_xboole_0(B_318))), inference(negUnitSimplification, [status(thm)], [c_116, c_140, c_910])).
% 13.60/5.54  tff(c_48, plain, (![F_141]: (k1_funct_1('#skF_8', F_141)!='#skF_9' | ~r2_hidden(F_141, '#skF_7') | ~r2_hidden(F_141, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 13.60/5.54  tff(c_1220, plain, (![E_319]: (k1_funct_1('#skF_8', '#skF_4'('#skF_7', E_319, '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~r2_hidden('#skF_4'('#skF_7', E_319, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_319, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_319, '#skF_6') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_1147, c_48])).
% 13.60/5.54  tff(c_1629, plain, (![E_358]: (k1_funct_1('#skF_8', '#skF_4'('#skF_7', E_358, '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~r2_hidden('#skF_4'('#skF_7', E_358, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_358, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_358, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_404, c_1220])).
% 13.60/5.54  tff(c_1632, plain, (![E_358]: (k1_funct_1('#skF_8', '#skF_4'('#skF_7', E_358, '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~r2_hidden(E_358, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_358, '#skF_6') | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4'('#skF_7', E_358, '#skF_8', '#skF_6', '#skF_5'), '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_1629])).
% 13.60/5.54  tff(c_9297, plain, (![E_814]: (k1_funct_1('#skF_8', '#skF_4'('#skF_7', E_814, '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~r2_hidden(E_814, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_814, '#skF_6') | ~m1_subset_1('#skF_4'('#skF_7', E_814, '#skF_8', '#skF_6', '#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_140, c_1632])).
% 13.60/5.54  tff(c_9348, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | ~m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_378, c_9297])).
% 13.60/5.54  tff(c_9400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1844, c_445, c_6428, c_9348])).
% 13.60/5.54  tff(c_9402, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_132])).
% 13.60/5.54  tff(c_8, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5), k1_zfmisc_1(A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.60/5.54  tff(c_9446, plain, (![A_822, B_823]: (v1_xboole_0('#skF_2'(k2_zfmisc_1(A_822, B_823))) | ~v1_xboole_0(A_822) | v1_xboole_0(k2_zfmisc_1(A_822, B_823)))), inference(resolution, [status(thm)], [c_8, c_123])).
% 13.60/5.54  tff(c_6, plain, (![A_5]: (~v1_xboole_0('#skF_2'(A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.60/5.54  tff(c_9451, plain, (![A_824, B_825]: (~v1_xboole_0(A_824) | v1_xboole_0(k2_zfmisc_1(A_824, B_825)))), inference(resolution, [status(thm)], [c_9446, c_6])).
% 13.60/5.54  tff(c_85, plain, (![B_151, A_152]: (v1_xboole_0(B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(A_152)) | ~v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.60/5.54  tff(c_93, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_85])).
% 13.60/5.54  tff(c_94, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_93])).
% 13.60/5.54  tff(c_9454, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_9451, c_94])).
% 13.60/5.54  tff(c_9458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9402, c_9454])).
% 13.60/5.54  tff(c_9460, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_115])).
% 13.60/5.54  tff(c_9534, plain, (![B_837, A_838]: (v1_xboole_0('#skF_2'(k2_zfmisc_1(B_837, A_838))) | ~v1_xboole_0(A_838) | v1_xboole_0(k2_zfmisc_1(B_837, A_838)))), inference(resolution, [status(thm)], [c_8, c_106])).
% 13.60/5.54  tff(c_9539, plain, (![A_839, B_840]: (~v1_xboole_0(A_839) | v1_xboole_0(k2_zfmisc_1(B_840, A_839)))), inference(resolution, [status(thm)], [c_9534, c_6])).
% 13.60/5.54  tff(c_9542, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_9539, c_94])).
% 13.60/5.54  tff(c_9546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9460, c_9542])).
% 13.60/5.54  tff(c_9547, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_93])).
% 13.60/5.54  tff(c_9899, plain, (![A_916, C_917]: (r2_hidden(k4_tarski(A_916, k1_funct_1(C_917, A_916)), C_917) | ~r2_hidden(A_916, k1_relat_1(C_917)) | ~v1_funct_1(C_917) | ~v1_relat_1(C_917))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.60/5.54  tff(c_9953, plain, (![C_918, A_919]: (~v1_xboole_0(C_918) | ~r2_hidden(A_919, k1_relat_1(C_918)) | ~v1_funct_1(C_918) | ~v1_relat_1(C_918))), inference(resolution, [status(thm)], [c_9899, c_2])).
% 13.60/5.54  tff(c_9978, plain, (![C_920]: (~v1_xboole_0(C_920) | ~v1_funct_1(C_920) | ~v1_relat_1(C_920) | v1_xboole_0(k1_relat_1(C_920)))), inference(resolution, [status(thm)], [c_4, c_9953])).
% 13.60/5.54  tff(c_9740, plain, (![A_890, B_891, C_892]: (r2_hidden('#skF_3'(A_890, B_891, C_892), k1_relat_1(C_892)) | ~r2_hidden(A_890, k9_relat_1(C_892, B_891)) | ~v1_relat_1(C_892))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.60/5.54  tff(c_9745, plain, (![C_893, A_894, B_895]: (~v1_xboole_0(k1_relat_1(C_893)) | ~r2_hidden(A_894, k9_relat_1(C_893, B_895)) | ~v1_relat_1(C_893))), inference(resolution, [status(thm)], [c_9740, c_2])).
% 13.60/5.54  tff(c_9760, plain, (![C_893, B_895]: (~v1_xboole_0(k1_relat_1(C_893)) | ~v1_relat_1(C_893) | v1_xboole_0(k9_relat_1(C_893, B_895)))), inference(resolution, [status(thm)], [c_4, c_9745])).
% 13.60/5.54  tff(c_9764, plain, (![A_901, B_902, C_903, D_904]: (k7_relset_1(A_901, B_902, C_903, D_904)=k9_relat_1(C_903, D_904) | ~m1_subset_1(C_903, k1_zfmisc_1(k2_zfmisc_1(A_901, B_902))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.60/5.54  tff(c_9775, plain, (![D_904]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_904)=k9_relat_1('#skF_8', D_904))), inference(resolution, [status(thm)], [c_52, c_9764])).
% 13.60/5.54  tff(c_9776, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_9775, c_68])).
% 13.60/5.54  tff(c_9789, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_9760, c_9776])).
% 13.60/5.54  tff(c_9795, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_9789])).
% 13.60/5.54  tff(c_9981, plain, (~v1_xboole_0('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_9978, c_9795])).
% 13.60/5.54  tff(c_9985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_9547, c_9981])).
% 13.60/5.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.60/5.54  
% 13.60/5.54  Inference rules
% 13.60/5.54  ----------------------
% 13.60/5.54  #Ref     : 0
% 13.60/5.54  #Sup     : 1989
% 13.60/5.54  #Fact    : 0
% 13.60/5.54  #Define  : 0
% 13.60/5.55  #Split   : 41
% 13.60/5.55  #Chain   : 0
% 13.60/5.55  #Close   : 0
% 13.60/5.55  
% 13.60/5.55  Ordering : KBO
% 13.60/5.55  
% 13.60/5.55  Simplification rules
% 13.60/5.55  ----------------------
% 13.60/5.55  #Subsume      : 596
% 13.60/5.55  #Demod        : 658
% 13.60/5.55  #Tautology    : 133
% 13.60/5.55  #SimpNegUnit  : 227
% 13.60/5.55  #BackRed      : 6
% 13.60/5.55  
% 13.60/5.55  #Partial instantiations: 0
% 13.60/5.55  #Strategies tried      : 1
% 13.60/5.55  
% 13.60/5.55  Timing (in seconds)
% 13.60/5.55  ----------------------
% 13.60/5.55  Preprocessing        : 0.56
% 13.60/5.55  Parsing              : 0.28
% 13.60/5.55  CNF conversion       : 0.06
% 13.60/5.55  Main loop            : 4.08
% 13.60/5.55  Inferencing          : 1.21
% 13.60/5.55  Reduction            : 1.05
% 13.60/5.55  Demodulation         : 0.70
% 13.60/5.55  BG Simplification    : 0.12
% 13.60/5.55  Subsumption          : 1.41
% 13.60/5.55  Abstraction          : 0.15
% 13.60/5.55  MUC search           : 0.00
% 13.60/5.55  Cooper               : 0.00
% 13.60/5.55  Total                : 4.72
% 13.60/5.55  Index Insertion      : 0.00
% 13.60/5.55  Index Deletion       : 0.00
% 13.60/5.55  Index Matching       : 0.00
% 13.60/5.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
