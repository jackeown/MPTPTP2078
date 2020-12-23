%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 13.06s
% Output     : CNFRefutation 13.06s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 801 expanded)
%              Number of leaves         :   39 ( 291 expanded)
%              Depth                    :   15
%              Number of atoms          :  377 (2244 expanded)
%              Number of equality atoms :   26 ( 244 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_153,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_98,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_134,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_18,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_88,plain,(
    ! [B_156,A_157] :
      ( v1_relat_1(B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_157))
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_94,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_91])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [A_205,B_206,C_207] :
      ( r2_hidden('#skF_3'(A_205,B_206,C_207),B_206)
      | ~ r2_hidden(A_205,k9_relat_1(C_207,B_206))
      | ~ v1_relat_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [B_208,A_209,C_210] :
      ( ~ v1_xboole_0(B_208)
      | ~ r2_hidden(A_209,k9_relat_1(C_210,B_208))
      | ~ v1_relat_1(C_210) ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_286,plain,(
    ! [B_208,C_210] :
      ( ~ v1_xboole_0(B_208)
      | ~ v1_relat_1(C_210)
      | v1_xboole_0(k9_relat_1(C_210,B_208)) ) ),
    inference(resolution,[status(thm)],[c_4,c_256])).

tff(c_405,plain,(
    ! [A_239,B_240,C_241,D_242] :
      ( k7_relset_1(A_239,B_240,C_241,D_242) = k9_relat_1(C_241,D_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_412,plain,(
    ! [D_242] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_242) = k9_relat_1('#skF_8',D_242) ),
    inference(resolution,[status(thm)],[c_56,c_405])).

tff(c_54,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_71,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_414,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_71])).

tff(c_432,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_286,c_414])).

tff(c_435,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_432])).

tff(c_415,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_54])).

tff(c_416,plain,(
    ! [D_243] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_243) = k9_relat_1('#skF_8',D_243) ),
    inference(resolution,[status(thm)],[c_56,c_405])).

tff(c_38,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( m1_subset_1(k7_relset_1(A_37,B_38,C_39,D_40),k1_zfmisc_1(B_38))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_422,plain,(
    ! [D_243] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_243),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_38])).

tff(c_457,plain,(
    ! [D_247] : m1_subset_1(k9_relat_1('#skF_8',D_247),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_422])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_486,plain,(
    ! [A_251,D_252] :
      ( m1_subset_1(A_251,'#skF_6')
      | ~ r2_hidden(A_251,k9_relat_1('#skF_8',D_252)) ) ),
    inference(resolution,[status(thm)],[c_457,c_14])).

tff(c_514,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_415,c_486])).

tff(c_170,plain,(
    ! [C_177,B_178,A_179] :
      ( v1_xboole_0(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(B_178,A_179)))
      | ~ v1_xboole_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_174,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_170])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_176,plain,(
    ! [C_180,A_181,B_182] :
      ( v1_xboole_0(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_xboole_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_181,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_1401,plain,(
    ! [E_328,C_331,B_327,A_330,D_329] :
      ( r2_hidden('#skF_4'(B_327,E_328,D_329,A_330,C_331),B_327)
      | ~ r2_hidden(E_328,k7_relset_1(C_331,A_330,D_329,B_327))
      | ~ m1_subset_1(E_328,A_330)
      | ~ m1_subset_1(D_329,k1_zfmisc_1(k2_zfmisc_1(C_331,A_330)))
      | v1_xboole_0(C_331)
      | v1_xboole_0(B_327)
      | v1_xboole_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1406,plain,(
    ! [B_327,E_328] :
      ( r2_hidden('#skF_4'(B_327,E_328,'#skF_8','#skF_6','#skF_5'),B_327)
      | ~ r2_hidden(E_328,k7_relset_1('#skF_5','#skF_6','#skF_8',B_327))
      | ~ m1_subset_1(E_328,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_327)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_1401])).

tff(c_1409,plain,(
    ! [B_327,E_328] :
      ( r2_hidden('#skF_4'(B_327,E_328,'#skF_8','#skF_6','#skF_5'),B_327)
      | ~ r2_hidden(E_328,k9_relat_1('#skF_8',B_327))
      | ~ m1_subset_1(E_328,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_327)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_1406])).

tff(c_4356,plain,(
    ! [B_617,E_618] :
      ( r2_hidden('#skF_4'(B_617,E_618,'#skF_8','#skF_6','#skF_5'),B_617)
      | ~ r2_hidden(E_618,k9_relat_1('#skF_8',B_617))
      | ~ m1_subset_1(E_618,'#skF_6')
      | v1_xboole_0(B_617) ) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_181,c_1409])).

tff(c_52,plain,(
    ! [F_147] :
      ( k1_funct_1('#skF_8',F_147) != '#skF_9'
      | ~ r2_hidden(F_147,'#skF_7')
      | ~ m1_subset_1(F_147,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4435,plain,(
    ! [E_618] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_7',E_618,'#skF_8','#skF_6','#skF_5')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_7',E_618,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_618,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_618,'#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4356,c_52])).

tff(c_4570,plain,(
    ! [E_626] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_7',E_626,'#skF_8','#skF_6','#skF_5')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_7',E_626,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_626,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_626,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_4435])).

tff(c_4621,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_415,c_4570])).

tff(c_4664,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_4621])).

tff(c_11190,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4664])).

tff(c_101,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_2'(A_160,B_161),A_160)
      | r1_tarski(A_160,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_160] : r1_tarski(A_160,A_160) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_436,plain,(
    ! [A_244,B_245,C_246] :
      ( r2_hidden('#skF_3'(A_244,B_245,C_246),k1_relat_1(C_246))
      | ~ r2_hidden(A_244,k9_relat_1(C_246,B_245))
      | ~ v1_relat_1(C_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_442,plain,(
    ! [A_244,B_245,C_246,B_6] :
      ( r2_hidden('#skF_3'(A_244,B_245,C_246),B_6)
      | ~ r1_tarski(k1_relat_1(C_246),B_6)
      | ~ r2_hidden(A_244,k9_relat_1(C_246,B_245))
      | ~ v1_relat_1(C_246) ) ),
    inference(resolution,[status(thm)],[c_436,c_6])).

tff(c_924,plain,(
    ! [A_287,B_288,C_289] :
      ( r2_hidden(k4_tarski('#skF_3'(A_287,B_288,C_289),A_287),C_289)
      | ~ r2_hidden(A_287,k9_relat_1(C_289,B_288))
      | ~ v1_relat_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [C_28,A_26,B_27] :
      ( k1_funct_1(C_28,A_26) = B_27
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2844,plain,(
    ! [C_495,A_496,B_497] :
      ( k1_funct_1(C_495,'#skF_3'(A_496,B_497,C_495)) = A_496
      | ~ v1_funct_1(C_495)
      | ~ r2_hidden(A_496,k9_relat_1(C_495,B_497))
      | ~ v1_relat_1(C_495) ) ),
    inference(resolution,[status(thm)],[c_924,c_30])).

tff(c_2866,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_415,c_2844])).

tff(c_2894,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60,c_2866])).

tff(c_28,plain,(
    ! [A_26,C_28] :
      ( r2_hidden(k4_tarski(A_26,k1_funct_1(C_28,A_26)),C_28)
      | ~ r2_hidden(A_26,k1_relat_1(C_28))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2904,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2894,c_28])).

tff(c_2908,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60,c_2904])).

tff(c_3175,plain,(
    ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2908])).

tff(c_3178,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_442,c_3175])).

tff(c_3191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_415,c_113,c_3178])).

tff(c_3192,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2908])).

tff(c_3580,plain,(
    ! [B_540] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_540)
      | ~ r1_tarski('#skF_8',B_540) ) ),
    inference(resolution,[status(thm)],[c_3192,c_6])).

tff(c_32,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3689,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_540))
      | ~ v1_funct_1(B_540)
      | ~ v1_relat_1(B_540)
      | ~ r1_tarski('#skF_8',B_540) ) ),
    inference(resolution,[status(thm)],[c_3580,c_32])).

tff(c_3316,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_6)
      | ~ r1_tarski('#skF_8',B_6) ) ),
    inference(resolution,[status(thm)],[c_3192,c_6])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden('#skF_3'(A_20,B_21,C_22),B_21)
      | ~ r2_hidden(A_20,k9_relat_1(C_22,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1180,plain,(
    ! [A_310,C_311,B_312,D_313] :
      ( r2_hidden(A_310,k9_relat_1(C_311,B_312))
      | ~ r2_hidden(D_313,B_312)
      | ~ r2_hidden(k4_tarski(D_313,A_310),C_311)
      | ~ r2_hidden(D_313,k1_relat_1(C_311))
      | ~ v1_relat_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6701,plain,(
    ! [A_793,A_795,C_792,B_794,C_791] :
      ( r2_hidden(A_793,k9_relat_1(C_792,B_794))
      | ~ r2_hidden(k4_tarski('#skF_3'(A_795,B_794,C_791),A_793),C_792)
      | ~ r2_hidden('#skF_3'(A_795,B_794,C_791),k1_relat_1(C_792))
      | ~ v1_relat_1(C_792)
      | ~ r2_hidden(A_795,k9_relat_1(C_791,B_794))
      | ~ v1_relat_1(C_791) ) ),
    inference(resolution,[status(thm)],[c_22,c_1180])).

tff(c_6708,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_9',k9_relat_1(B_6,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',B_6) ) ),
    inference(resolution,[status(thm)],[c_3316,c_6701])).

tff(c_11255,plain,(
    ! [B_1105] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1105,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1105))
      | ~ v1_relat_1(B_1105)
      | ~ r1_tarski('#skF_8',B_1105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_415,c_6708])).

tff(c_11278,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_9',k9_relat_1(B_540,'#skF_7'))
      | ~ v1_funct_1(B_540)
      | ~ v1_relat_1(B_540)
      | ~ r1_tarski('#skF_8',B_540) ) ),
    inference(resolution,[status(thm)],[c_3689,c_11255])).

tff(c_1482,plain,(
    ! [A_342,E_340,B_339,C_343,D_341] :
      ( m1_subset_1('#skF_4'(B_339,E_340,D_341,A_342,C_343),C_343)
      | ~ r2_hidden(E_340,k7_relset_1(C_343,A_342,D_341,B_339))
      | ~ m1_subset_1(E_340,A_342)
      | ~ m1_subset_1(D_341,k1_zfmisc_1(k2_zfmisc_1(C_343,A_342)))
      | v1_xboole_0(C_343)
      | v1_xboole_0(B_339)
      | v1_xboole_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1493,plain,(
    ! [D_242,E_340] :
      ( m1_subset_1('#skF_4'(D_242,E_340,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_340,k9_relat_1('#skF_8',D_242))
      | ~ m1_subset_1(E_340,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_242)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_1482])).

tff(c_1516,plain,(
    ! [D_242,E_340] :
      ( m1_subset_1('#skF_4'(D_242,E_340,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_340,k9_relat_1('#skF_8',D_242))
      | ~ m1_subset_1(E_340,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_242)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1493])).

tff(c_13768,plain,(
    ! [D_1240,E_1241] :
      ( m1_subset_1('#skF_4'(D_1240,E_1241,'#skF_8','#skF_6','#skF_5'),'#skF_5')
      | ~ r2_hidden(E_1241,k9_relat_1('#skF_8',D_1240))
      | ~ m1_subset_1(E_1241,'#skF_6')
      | v1_xboole_0(D_1240) ) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_181,c_1516])).

tff(c_13792,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_11278,c_13768])).

tff(c_13900,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_94,c_60,c_514,c_13792])).

tff(c_13902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_11190,c_13900])).

tff(c_13903,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4664])).

tff(c_13963,plain,(
    ! [B_1265] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1265,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1265))
      | ~ v1_relat_1(B_1265)
      | ~ r1_tarski('#skF_8',B_1265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_415,c_6708])).

tff(c_13986,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_9',k9_relat_1(B_540,'#skF_7'))
      | ~ v1_funct_1(B_540)
      | ~ v1_relat_1(B_540)
      | ~ r1_tarski('#skF_8',B_540) ) ),
    inference(resolution,[status(thm)],[c_3689,c_13963])).

tff(c_1584,plain,(
    ! [E_356,D_357,A_358,B_355,C_359] :
      ( r2_hidden(k4_tarski('#skF_4'(B_355,E_356,D_357,A_358,C_359),E_356),D_357)
      | ~ r2_hidden(E_356,k7_relset_1(C_359,A_358,D_357,B_355))
      | ~ m1_subset_1(E_356,A_358)
      | ~ m1_subset_1(D_357,k1_zfmisc_1(k2_zfmisc_1(C_359,A_358)))
      | v1_xboole_0(C_359)
      | v1_xboole_0(B_355)
      | v1_xboole_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7983,plain,(
    ! [D_898,A_895,C_896,E_894,B_897] :
      ( k1_funct_1(D_898,'#skF_4'(B_897,E_894,D_898,A_895,C_896)) = E_894
      | ~ v1_funct_1(D_898)
      | ~ v1_relat_1(D_898)
      | ~ r2_hidden(E_894,k7_relset_1(C_896,A_895,D_898,B_897))
      | ~ m1_subset_1(E_894,A_895)
      | ~ m1_subset_1(D_898,k1_zfmisc_1(k2_zfmisc_1(C_896,A_895)))
      | v1_xboole_0(C_896)
      | v1_xboole_0(B_897)
      | v1_xboole_0(A_895) ) ),
    inference(resolution,[status(thm)],[c_1584,c_30])).

tff(c_8034,plain,(
    ! [D_242,E_894] :
      ( k1_funct_1('#skF_8','#skF_4'(D_242,E_894,'#skF_8','#skF_6','#skF_5')) = E_894
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(E_894,k9_relat_1('#skF_8',D_242))
      | ~ m1_subset_1(E_894,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_242)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_7983])).

tff(c_8076,plain,(
    ! [D_242,E_894] :
      ( k1_funct_1('#skF_8','#skF_4'(D_242,E_894,'#skF_8','#skF_6','#skF_5')) = E_894
      | ~ r2_hidden(E_894,k9_relat_1('#skF_8',D_242))
      | ~ m1_subset_1(E_894,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_242)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_94,c_60,c_8034])).

tff(c_21159,plain,(
    ! [D_1620,E_1621] :
      ( k1_funct_1('#skF_8','#skF_4'(D_1620,E_1621,'#skF_8','#skF_6','#skF_5')) = E_1621
      | ~ r2_hidden(E_1621,k9_relat_1('#skF_8',D_1620))
      | ~ m1_subset_1(E_1621,'#skF_6')
      | v1_xboole_0(D_1620) ) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_181,c_8076])).

tff(c_21199,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) = '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_13986,c_21159])).

tff(c_21322,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_7','#skF_9','#skF_8','#skF_6','#skF_5')) = '#skF_9'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_94,c_60,c_514,c_21199])).

tff(c_21324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_13903,c_21322])).

tff(c_21325,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_21666,plain,(
    ! [A_1692,C_1693] :
      ( r2_hidden(k4_tarski(A_1692,k1_funct_1(C_1693,A_1692)),C_1693)
      | ~ r2_hidden(A_1692,k1_relat_1(C_1693))
      | ~ v1_funct_1(C_1693)
      | ~ v1_relat_1(C_1693) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_21794,plain,(
    ! [C_1701,A_1702] :
      ( ~ v1_xboole_0(C_1701)
      | ~ r2_hidden(A_1702,k1_relat_1(C_1701))
      | ~ v1_funct_1(C_1701)
      | ~ v1_relat_1(C_1701) ) ),
    inference(resolution,[status(thm)],[c_21666,c_2])).

tff(c_21834,plain,(
    ! [C_1703] :
      ( ~ v1_xboole_0(C_1703)
      | ~ v1_funct_1(C_1703)
      | ~ v1_relat_1(C_1703)
      | v1_xboole_0(k1_relat_1(C_1703)) ) ),
    inference(resolution,[status(thm)],[c_4,c_21794])).

tff(c_21550,plain,(
    ! [A_1678,B_1679,C_1680,D_1681] :
      ( k7_relset_1(A_1678,B_1679,C_1680,D_1681) = k9_relat_1(C_1680,D_1681)
      | ~ m1_subset_1(C_1680,k1_zfmisc_1(k2_zfmisc_1(A_1678,B_1679))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_21557,plain,(
    ! [D_1681] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_1681) = k9_relat_1('#skF_8',D_1681) ),
    inference(resolution,[status(thm)],[c_56,c_21550])).

tff(c_21560,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21557,c_54])).

tff(c_21581,plain,(
    ! [A_1683,B_1684,C_1685] :
      ( r2_hidden('#skF_3'(A_1683,B_1684,C_1685),k1_relat_1(C_1685))
      | ~ r2_hidden(A_1683,k9_relat_1(C_1685,B_1684))
      | ~ v1_relat_1(C_1685) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_21703,plain,(
    ! [C_1694,A_1695,B_1696] :
      ( ~ v1_xboole_0(k1_relat_1(C_1694))
      | ~ r2_hidden(A_1695,k9_relat_1(C_1694,B_1696))
      | ~ v1_relat_1(C_1694) ) ),
    inference(resolution,[status(thm)],[c_21581,c_2])).

tff(c_21710,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_21560,c_21703])).

tff(c_21738,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_21710])).

tff(c_21837,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_21834,c_21738])).

tff(c_21841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60,c_21325,c_21837])).

tff(c_21842,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_22226,plain,(
    ! [A_1780,C_1781] :
      ( r2_hidden(k4_tarski(A_1780,k1_funct_1(C_1781,A_1780)),C_1781)
      | ~ r2_hidden(A_1780,k1_relat_1(C_1781))
      | ~ v1_funct_1(C_1781)
      | ~ v1_relat_1(C_1781) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22275,plain,(
    ! [C_1784,A_1785] :
      ( ~ v1_xboole_0(C_1784)
      | ~ r2_hidden(A_1785,k1_relat_1(C_1784))
      | ~ v1_funct_1(C_1784)
      | ~ v1_relat_1(C_1784) ) ),
    inference(resolution,[status(thm)],[c_22226,c_2])).

tff(c_22357,plain,(
    ! [C_1788] :
      ( ~ v1_xboole_0(C_1788)
      | ~ v1_funct_1(C_1788)
      | ~ v1_relat_1(C_1788)
      | v1_xboole_0(k1_relat_1(C_1788)) ) ),
    inference(resolution,[status(thm)],[c_4,c_22275])).

tff(c_22073,plain,(
    ! [A_1763,B_1764,C_1765,D_1766] :
      ( k7_relset_1(A_1763,B_1764,C_1765,D_1766) = k9_relat_1(C_1765,D_1766)
      | ~ m1_subset_1(C_1765,k1_zfmisc_1(k2_zfmisc_1(A_1763,B_1764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22080,plain,(
    ! [D_1766] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_1766) = k9_relat_1('#skF_8',D_1766) ),
    inference(resolution,[status(thm)],[c_56,c_22073])).

tff(c_22083,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22080,c_54])).

tff(c_22117,plain,(
    ! [A_1768,B_1769,C_1770] :
      ( r2_hidden('#skF_3'(A_1768,B_1769,C_1770),k1_relat_1(C_1770))
      | ~ r2_hidden(A_1768,k9_relat_1(C_1770,B_1769))
      | ~ v1_relat_1(C_1770) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22189,plain,(
    ! [C_1777,A_1778,B_1779] :
      ( ~ v1_xboole_0(k1_relat_1(C_1777))
      | ~ r2_hidden(A_1778,k9_relat_1(C_1777,B_1779))
      | ~ v1_relat_1(C_1777) ) ),
    inference(resolution,[status(thm)],[c_22117,c_2])).

tff(c_22192,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_22083,c_22189])).

tff(c_22219,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_22192])).

tff(c_22360,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_22357,c_22219])).

tff(c_22364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60,c_21842,c_22360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.06/5.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.06/5.94  
% 13.06/5.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.06/5.95  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 13.06/5.95  
% 13.06/5.95  %Foreground sorts:
% 13.06/5.95  
% 13.06/5.95  
% 13.06/5.95  %Background operators:
% 13.06/5.95  
% 13.06/5.95  
% 13.06/5.95  %Foreground operators:
% 13.06/5.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.06/5.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.06/5.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.06/5.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.06/5.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.06/5.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 13.06/5.95  tff('#skF_7', type, '#skF_7': $i).
% 13.06/5.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.06/5.95  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.06/5.95  tff('#skF_5', type, '#skF_5': $i).
% 13.06/5.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.06/5.95  tff('#skF_6', type, '#skF_6': $i).
% 13.06/5.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.06/5.95  tff('#skF_9', type, '#skF_9': $i).
% 13.06/5.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.06/5.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.06/5.95  tff('#skF_8', type, '#skF_8': $i).
% 13.06/5.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.06/5.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.06/5.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.06/5.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.06/5.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.06/5.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.06/5.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.06/5.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.06/5.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.06/5.95  
% 13.06/5.97  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.06/5.97  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 13.06/5.97  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.06/5.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.06/5.97  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 13.06/5.97  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.06/5.97  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 13.06/5.97  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 13.06/5.97  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.06/5.97  tff(f_87, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 13.06/5.97  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 13.06/5.97  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.06/5.97  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 13.06/5.97  tff(c_18, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.06/5.97  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.06/5.97  tff(c_88, plain, (![B_156, A_157]: (v1_relat_1(B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(A_157)) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.06/5.97  tff(c_91, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_88])).
% 13.06/5.97  tff(c_94, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_91])).
% 13.06/5.97  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.06/5.97  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.06/5.97  tff(c_243, plain, (![A_205, B_206, C_207]: (r2_hidden('#skF_3'(A_205, B_206, C_207), B_206) | ~r2_hidden(A_205, k9_relat_1(C_207, B_206)) | ~v1_relat_1(C_207))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.06/5.97  tff(c_256, plain, (![B_208, A_209, C_210]: (~v1_xboole_0(B_208) | ~r2_hidden(A_209, k9_relat_1(C_210, B_208)) | ~v1_relat_1(C_210))), inference(resolution, [status(thm)], [c_243, c_2])).
% 13.06/5.97  tff(c_286, plain, (![B_208, C_210]: (~v1_xboole_0(B_208) | ~v1_relat_1(C_210) | v1_xboole_0(k9_relat_1(C_210, B_208)))), inference(resolution, [status(thm)], [c_4, c_256])).
% 13.06/5.97  tff(c_405, plain, (![A_239, B_240, C_241, D_242]: (k7_relset_1(A_239, B_240, C_241, D_242)=k9_relat_1(C_241, D_242) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.06/5.97  tff(c_412, plain, (![D_242]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_242)=k9_relat_1('#skF_8', D_242))), inference(resolution, [status(thm)], [c_56, c_405])).
% 13.06/5.97  tff(c_54, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.06/5.97  tff(c_71, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 13.06/5.97  tff(c_414, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_71])).
% 13.06/5.97  tff(c_432, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_286, c_414])).
% 13.06/5.97  tff(c_435, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_432])).
% 13.06/5.97  tff(c_415, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_54])).
% 13.06/5.97  tff(c_416, plain, (![D_243]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_243)=k9_relat_1('#skF_8', D_243))), inference(resolution, [status(thm)], [c_56, c_405])).
% 13.06/5.97  tff(c_38, plain, (![A_37, B_38, C_39, D_40]: (m1_subset_1(k7_relset_1(A_37, B_38, C_39, D_40), k1_zfmisc_1(B_38)) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.06/5.97  tff(c_422, plain, (![D_243]: (m1_subset_1(k9_relat_1('#skF_8', D_243), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_416, c_38])).
% 13.06/5.97  tff(c_457, plain, (![D_247]: (m1_subset_1(k9_relat_1('#skF_8', D_247), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_422])).
% 13.06/5.97  tff(c_14, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.06/5.97  tff(c_486, plain, (![A_251, D_252]: (m1_subset_1(A_251, '#skF_6') | ~r2_hidden(A_251, k9_relat_1('#skF_8', D_252)))), inference(resolution, [status(thm)], [c_457, c_14])).
% 13.06/5.97  tff(c_514, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_415, c_486])).
% 13.06/5.97  tff(c_170, plain, (![C_177, B_178, A_179]: (v1_xboole_0(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(B_178, A_179))) | ~v1_xboole_0(A_179))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.06/5.97  tff(c_174, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_170])).
% 13.06/5.97  tff(c_175, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_174])).
% 13.06/5.97  tff(c_176, plain, (![C_180, A_181, B_182]: (v1_xboole_0(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_xboole_0(A_181))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.06/5.97  tff(c_180, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_176])).
% 13.06/5.97  tff(c_181, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_180])).
% 13.06/5.97  tff(c_1401, plain, (![E_328, C_331, B_327, A_330, D_329]: (r2_hidden('#skF_4'(B_327, E_328, D_329, A_330, C_331), B_327) | ~r2_hidden(E_328, k7_relset_1(C_331, A_330, D_329, B_327)) | ~m1_subset_1(E_328, A_330) | ~m1_subset_1(D_329, k1_zfmisc_1(k2_zfmisc_1(C_331, A_330))) | v1_xboole_0(C_331) | v1_xboole_0(B_327) | v1_xboole_0(A_330))), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.06/5.97  tff(c_1406, plain, (![B_327, E_328]: (r2_hidden('#skF_4'(B_327, E_328, '#skF_8', '#skF_6', '#skF_5'), B_327) | ~r2_hidden(E_328, k7_relset_1('#skF_5', '#skF_6', '#skF_8', B_327)) | ~m1_subset_1(E_328, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_327) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_1401])).
% 13.06/5.97  tff(c_1409, plain, (![B_327, E_328]: (r2_hidden('#skF_4'(B_327, E_328, '#skF_8', '#skF_6', '#skF_5'), B_327) | ~r2_hidden(E_328, k9_relat_1('#skF_8', B_327)) | ~m1_subset_1(E_328, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_327) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_1406])).
% 13.06/5.97  tff(c_4356, plain, (![B_617, E_618]: (r2_hidden('#skF_4'(B_617, E_618, '#skF_8', '#skF_6', '#skF_5'), B_617) | ~r2_hidden(E_618, k9_relat_1('#skF_8', B_617)) | ~m1_subset_1(E_618, '#skF_6') | v1_xboole_0(B_617))), inference(negUnitSimplification, [status(thm)], [c_175, c_181, c_1409])).
% 13.06/5.97  tff(c_52, plain, (![F_147]: (k1_funct_1('#skF_8', F_147)!='#skF_9' | ~r2_hidden(F_147, '#skF_7') | ~m1_subset_1(F_147, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.06/5.97  tff(c_4435, plain, (![E_618]: (k1_funct_1('#skF_8', '#skF_4'('#skF_7', E_618, '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_7', E_618, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_618, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_618, '#skF_6') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_4356, c_52])).
% 13.06/5.97  tff(c_4570, plain, (![E_626]: (k1_funct_1('#skF_8', '#skF_4'('#skF_7', E_626, '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_7', E_626, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_626, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_626, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_435, c_4435])).
% 13.06/5.97  tff(c_4621, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_415, c_4570])).
% 13.06/5.97  tff(c_4664, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_4621])).
% 13.06/5.97  tff(c_11190, plain, (~m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4664])).
% 13.06/5.97  tff(c_101, plain, (![A_160, B_161]: (r2_hidden('#skF_2'(A_160, B_161), A_160) | r1_tarski(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.06/5.97  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.06/5.97  tff(c_113, plain, (![A_160]: (r1_tarski(A_160, A_160))), inference(resolution, [status(thm)], [c_101, c_8])).
% 13.06/5.97  tff(c_436, plain, (![A_244, B_245, C_246]: (r2_hidden('#skF_3'(A_244, B_245, C_246), k1_relat_1(C_246)) | ~r2_hidden(A_244, k9_relat_1(C_246, B_245)) | ~v1_relat_1(C_246))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.06/5.97  tff(c_442, plain, (![A_244, B_245, C_246, B_6]: (r2_hidden('#skF_3'(A_244, B_245, C_246), B_6) | ~r1_tarski(k1_relat_1(C_246), B_6) | ~r2_hidden(A_244, k9_relat_1(C_246, B_245)) | ~v1_relat_1(C_246))), inference(resolution, [status(thm)], [c_436, c_6])).
% 13.06/5.97  tff(c_924, plain, (![A_287, B_288, C_289]: (r2_hidden(k4_tarski('#skF_3'(A_287, B_288, C_289), A_287), C_289) | ~r2_hidden(A_287, k9_relat_1(C_289, B_288)) | ~v1_relat_1(C_289))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_30, plain, (![C_28, A_26, B_27]: (k1_funct_1(C_28, A_26)=B_27 | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.06/5.97  tff(c_2844, plain, (![C_495, A_496, B_497]: (k1_funct_1(C_495, '#skF_3'(A_496, B_497, C_495))=A_496 | ~v1_funct_1(C_495) | ~r2_hidden(A_496, k9_relat_1(C_495, B_497)) | ~v1_relat_1(C_495))), inference(resolution, [status(thm)], [c_924, c_30])).
% 13.06/5.97  tff(c_2866, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_415, c_2844])).
% 13.06/5.97  tff(c_2894, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60, c_2866])).
% 13.06/5.97  tff(c_28, plain, (![A_26, C_28]: (r2_hidden(k4_tarski(A_26, k1_funct_1(C_28, A_26)), C_28) | ~r2_hidden(A_26, k1_relat_1(C_28)) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.06/5.97  tff(c_2904, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2894, c_28])).
% 13.06/5.97  tff(c_2908, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60, c_2904])).
% 13.06/5.97  tff(c_3175, plain, (~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_2908])).
% 13.06/5.97  tff(c_3178, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_442, c_3175])).
% 13.06/5.97  tff(c_3191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_415, c_113, c_3178])).
% 13.06/5.97  tff(c_3192, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_2908])).
% 13.06/5.97  tff(c_3580, plain, (![B_540]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_540) | ~r1_tarski('#skF_8', B_540))), inference(resolution, [status(thm)], [c_3192, c_6])).
% 13.06/5.97  tff(c_32, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.06/5.97  tff(c_3689, plain, (![B_540]: (r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_540)) | ~v1_funct_1(B_540) | ~v1_relat_1(B_540) | ~r1_tarski('#skF_8', B_540))), inference(resolution, [status(thm)], [c_3580, c_32])).
% 13.06/5.97  tff(c_3316, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_6) | ~r1_tarski('#skF_8', B_6))), inference(resolution, [status(thm)], [c_3192, c_6])).
% 13.06/5.97  tff(c_22, plain, (![A_20, B_21, C_22]: (r2_hidden('#skF_3'(A_20, B_21, C_22), B_21) | ~r2_hidden(A_20, k9_relat_1(C_22, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_1180, plain, (![A_310, C_311, B_312, D_313]: (r2_hidden(A_310, k9_relat_1(C_311, B_312)) | ~r2_hidden(D_313, B_312) | ~r2_hidden(k4_tarski(D_313, A_310), C_311) | ~r2_hidden(D_313, k1_relat_1(C_311)) | ~v1_relat_1(C_311))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_6701, plain, (![A_793, A_795, C_792, B_794, C_791]: (r2_hidden(A_793, k9_relat_1(C_792, B_794)) | ~r2_hidden(k4_tarski('#skF_3'(A_795, B_794, C_791), A_793), C_792) | ~r2_hidden('#skF_3'(A_795, B_794, C_791), k1_relat_1(C_792)) | ~v1_relat_1(C_792) | ~r2_hidden(A_795, k9_relat_1(C_791, B_794)) | ~v1_relat_1(C_791))), inference(resolution, [status(thm)], [c_22, c_1180])).
% 13.06/5.97  tff(c_6708, plain, (![B_6]: (r2_hidden('#skF_9', k9_relat_1(B_6, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_6)) | ~v1_relat_1(B_6) | ~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', B_6))), inference(resolution, [status(thm)], [c_3316, c_6701])).
% 13.06/5.97  tff(c_11255, plain, (![B_1105]: (r2_hidden('#skF_9', k9_relat_1(B_1105, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1105)) | ~v1_relat_1(B_1105) | ~r1_tarski('#skF_8', B_1105))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_415, c_6708])).
% 13.06/5.97  tff(c_11278, plain, (![B_540]: (r2_hidden('#skF_9', k9_relat_1(B_540, '#skF_7')) | ~v1_funct_1(B_540) | ~v1_relat_1(B_540) | ~r1_tarski('#skF_8', B_540))), inference(resolution, [status(thm)], [c_3689, c_11255])).
% 13.06/5.97  tff(c_1482, plain, (![A_342, E_340, B_339, C_343, D_341]: (m1_subset_1('#skF_4'(B_339, E_340, D_341, A_342, C_343), C_343) | ~r2_hidden(E_340, k7_relset_1(C_343, A_342, D_341, B_339)) | ~m1_subset_1(E_340, A_342) | ~m1_subset_1(D_341, k1_zfmisc_1(k2_zfmisc_1(C_343, A_342))) | v1_xboole_0(C_343) | v1_xboole_0(B_339) | v1_xboole_0(A_342))), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.06/5.97  tff(c_1493, plain, (![D_242, E_340]: (m1_subset_1('#skF_4'(D_242, E_340, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_340, k9_relat_1('#skF_8', D_242)) | ~m1_subset_1(E_340, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_242) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_1482])).
% 13.06/5.97  tff(c_1516, plain, (![D_242, E_340]: (m1_subset_1('#skF_4'(D_242, E_340, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_340, k9_relat_1('#skF_8', D_242)) | ~m1_subset_1(E_340, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_242) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1493])).
% 13.06/5.97  tff(c_13768, plain, (![D_1240, E_1241]: (m1_subset_1('#skF_4'(D_1240, E_1241, '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden(E_1241, k9_relat_1('#skF_8', D_1240)) | ~m1_subset_1(E_1241, '#skF_6') | v1_xboole_0(D_1240))), inference(negUnitSimplification, [status(thm)], [c_175, c_181, c_1516])).
% 13.06/5.97  tff(c_13792, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_11278, c_13768])).
% 13.06/5.97  tff(c_13900, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_94, c_60, c_514, c_13792])).
% 13.06/5.97  tff(c_13902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_11190, c_13900])).
% 13.06/5.97  tff(c_13903, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))!='#skF_9'), inference(splitRight, [status(thm)], [c_4664])).
% 13.06/5.97  tff(c_13963, plain, (![B_1265]: (r2_hidden('#skF_9', k9_relat_1(B_1265, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1265)) | ~v1_relat_1(B_1265) | ~r1_tarski('#skF_8', B_1265))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_415, c_6708])).
% 13.06/5.97  tff(c_13986, plain, (![B_540]: (r2_hidden('#skF_9', k9_relat_1(B_540, '#skF_7')) | ~v1_funct_1(B_540) | ~v1_relat_1(B_540) | ~r1_tarski('#skF_8', B_540))), inference(resolution, [status(thm)], [c_3689, c_13963])).
% 13.06/5.97  tff(c_1584, plain, (![E_356, D_357, A_358, B_355, C_359]: (r2_hidden(k4_tarski('#skF_4'(B_355, E_356, D_357, A_358, C_359), E_356), D_357) | ~r2_hidden(E_356, k7_relset_1(C_359, A_358, D_357, B_355)) | ~m1_subset_1(E_356, A_358) | ~m1_subset_1(D_357, k1_zfmisc_1(k2_zfmisc_1(C_359, A_358))) | v1_xboole_0(C_359) | v1_xboole_0(B_355) | v1_xboole_0(A_358))), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.06/5.97  tff(c_7983, plain, (![D_898, A_895, C_896, E_894, B_897]: (k1_funct_1(D_898, '#skF_4'(B_897, E_894, D_898, A_895, C_896))=E_894 | ~v1_funct_1(D_898) | ~v1_relat_1(D_898) | ~r2_hidden(E_894, k7_relset_1(C_896, A_895, D_898, B_897)) | ~m1_subset_1(E_894, A_895) | ~m1_subset_1(D_898, k1_zfmisc_1(k2_zfmisc_1(C_896, A_895))) | v1_xboole_0(C_896) | v1_xboole_0(B_897) | v1_xboole_0(A_895))), inference(resolution, [status(thm)], [c_1584, c_30])).
% 13.06/5.97  tff(c_8034, plain, (![D_242, E_894]: (k1_funct_1('#skF_8', '#skF_4'(D_242, E_894, '#skF_8', '#skF_6', '#skF_5'))=E_894 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(E_894, k9_relat_1('#skF_8', D_242)) | ~m1_subset_1(E_894, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_242) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_7983])).
% 13.06/5.97  tff(c_8076, plain, (![D_242, E_894]: (k1_funct_1('#skF_8', '#skF_4'(D_242, E_894, '#skF_8', '#skF_6', '#skF_5'))=E_894 | ~r2_hidden(E_894, k9_relat_1('#skF_8', D_242)) | ~m1_subset_1(E_894, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_242) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_94, c_60, c_8034])).
% 13.06/5.97  tff(c_21159, plain, (![D_1620, E_1621]: (k1_funct_1('#skF_8', '#skF_4'(D_1620, E_1621, '#skF_8', '#skF_6', '#skF_5'))=E_1621 | ~r2_hidden(E_1621, k9_relat_1('#skF_8', D_1620)) | ~m1_subset_1(E_1621, '#skF_6') | v1_xboole_0(D_1620))), inference(negUnitSimplification, [status(thm)], [c_175, c_181, c_8076])).
% 13.06/5.97  tff(c_21199, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_13986, c_21159])).
% 13.06/5.97  tff(c_21322, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_7', '#skF_9', '#skF_8', '#skF_6', '#skF_5'))='#skF_9' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_94, c_60, c_514, c_21199])).
% 13.06/5.97  tff(c_21324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_13903, c_21322])).
% 13.06/5.97  tff(c_21325, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_180])).
% 13.06/5.97  tff(c_21666, plain, (![A_1692, C_1693]: (r2_hidden(k4_tarski(A_1692, k1_funct_1(C_1693, A_1692)), C_1693) | ~r2_hidden(A_1692, k1_relat_1(C_1693)) | ~v1_funct_1(C_1693) | ~v1_relat_1(C_1693))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.06/5.97  tff(c_21794, plain, (![C_1701, A_1702]: (~v1_xboole_0(C_1701) | ~r2_hidden(A_1702, k1_relat_1(C_1701)) | ~v1_funct_1(C_1701) | ~v1_relat_1(C_1701))), inference(resolution, [status(thm)], [c_21666, c_2])).
% 13.06/5.97  tff(c_21834, plain, (![C_1703]: (~v1_xboole_0(C_1703) | ~v1_funct_1(C_1703) | ~v1_relat_1(C_1703) | v1_xboole_0(k1_relat_1(C_1703)))), inference(resolution, [status(thm)], [c_4, c_21794])).
% 13.06/5.97  tff(c_21550, plain, (![A_1678, B_1679, C_1680, D_1681]: (k7_relset_1(A_1678, B_1679, C_1680, D_1681)=k9_relat_1(C_1680, D_1681) | ~m1_subset_1(C_1680, k1_zfmisc_1(k2_zfmisc_1(A_1678, B_1679))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.06/5.97  tff(c_21557, plain, (![D_1681]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_1681)=k9_relat_1('#skF_8', D_1681))), inference(resolution, [status(thm)], [c_56, c_21550])).
% 13.06/5.97  tff(c_21560, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_21557, c_54])).
% 13.06/5.97  tff(c_21581, plain, (![A_1683, B_1684, C_1685]: (r2_hidden('#skF_3'(A_1683, B_1684, C_1685), k1_relat_1(C_1685)) | ~r2_hidden(A_1683, k9_relat_1(C_1685, B_1684)) | ~v1_relat_1(C_1685))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_21703, plain, (![C_1694, A_1695, B_1696]: (~v1_xboole_0(k1_relat_1(C_1694)) | ~r2_hidden(A_1695, k9_relat_1(C_1694, B_1696)) | ~v1_relat_1(C_1694))), inference(resolution, [status(thm)], [c_21581, c_2])).
% 13.06/5.97  tff(c_21710, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_21560, c_21703])).
% 13.06/5.97  tff(c_21738, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_21710])).
% 13.06/5.97  tff(c_21837, plain, (~v1_xboole_0('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_21834, c_21738])).
% 13.06/5.97  tff(c_21841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_60, c_21325, c_21837])).
% 13.06/5.97  tff(c_21842, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_174])).
% 13.06/5.97  tff(c_22226, plain, (![A_1780, C_1781]: (r2_hidden(k4_tarski(A_1780, k1_funct_1(C_1781, A_1780)), C_1781) | ~r2_hidden(A_1780, k1_relat_1(C_1781)) | ~v1_funct_1(C_1781) | ~v1_relat_1(C_1781))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.06/5.97  tff(c_22275, plain, (![C_1784, A_1785]: (~v1_xboole_0(C_1784) | ~r2_hidden(A_1785, k1_relat_1(C_1784)) | ~v1_funct_1(C_1784) | ~v1_relat_1(C_1784))), inference(resolution, [status(thm)], [c_22226, c_2])).
% 13.06/5.97  tff(c_22357, plain, (![C_1788]: (~v1_xboole_0(C_1788) | ~v1_funct_1(C_1788) | ~v1_relat_1(C_1788) | v1_xboole_0(k1_relat_1(C_1788)))), inference(resolution, [status(thm)], [c_4, c_22275])).
% 13.06/5.97  tff(c_22073, plain, (![A_1763, B_1764, C_1765, D_1766]: (k7_relset_1(A_1763, B_1764, C_1765, D_1766)=k9_relat_1(C_1765, D_1766) | ~m1_subset_1(C_1765, k1_zfmisc_1(k2_zfmisc_1(A_1763, B_1764))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.06/5.97  tff(c_22080, plain, (![D_1766]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_1766)=k9_relat_1('#skF_8', D_1766))), inference(resolution, [status(thm)], [c_56, c_22073])).
% 13.06/5.97  tff(c_22083, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22080, c_54])).
% 13.06/5.97  tff(c_22117, plain, (![A_1768, B_1769, C_1770]: (r2_hidden('#skF_3'(A_1768, B_1769, C_1770), k1_relat_1(C_1770)) | ~r2_hidden(A_1768, k9_relat_1(C_1770, B_1769)) | ~v1_relat_1(C_1770))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.06/5.97  tff(c_22189, plain, (![C_1777, A_1778, B_1779]: (~v1_xboole_0(k1_relat_1(C_1777)) | ~r2_hidden(A_1778, k9_relat_1(C_1777, B_1779)) | ~v1_relat_1(C_1777))), inference(resolution, [status(thm)], [c_22117, c_2])).
% 13.06/5.97  tff(c_22192, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_22083, c_22189])).
% 13.06/5.97  tff(c_22219, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_22192])).
% 13.06/5.97  tff(c_22360, plain, (~v1_xboole_0('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_22357, c_22219])).
% 13.06/5.97  tff(c_22364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_60, c_21842, c_22360])).
% 13.06/5.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.06/5.97  
% 13.06/5.97  Inference rules
% 13.06/5.97  ----------------------
% 13.06/5.97  #Ref     : 0
% 13.06/5.97  #Sup     : 4950
% 13.06/5.97  #Fact    : 0
% 13.06/5.97  #Define  : 0
% 13.06/5.97  #Split   : 40
% 13.06/5.97  #Chain   : 0
% 13.06/5.97  #Close   : 0
% 13.06/5.97  
% 13.06/5.97  Ordering : KBO
% 13.06/5.97  
% 13.06/5.97  Simplification rules
% 13.06/5.97  ----------------------
% 13.06/5.97  #Subsume      : 2256
% 13.06/5.98  #Demod        : 784
% 13.06/5.98  #Tautology    : 185
% 13.06/5.98  #SimpNegUnit  : 143
% 13.06/5.98  #BackRed      : 9
% 13.06/5.98  
% 13.06/5.98  #Partial instantiations: 0
% 13.06/5.98  #Strategies tried      : 1
% 13.06/5.98  
% 13.06/5.98  Timing (in seconds)
% 13.06/5.98  ----------------------
% 13.06/5.98  Preprocessing        : 0.35
% 13.06/5.98  Parsing              : 0.18
% 13.06/5.98  CNF conversion       : 0.04
% 13.06/5.98  Main loop            : 4.79
% 13.06/5.98  Inferencing          : 1.06
% 13.06/5.98  Reduction            : 1.07
% 13.06/5.98  Demodulation         : 0.72
% 13.06/5.98  BG Simplification    : 0.08
% 13.06/5.98  Subsumption          : 2.29
% 13.06/5.98  Abstraction          : 0.13
% 13.06/5.98  MUC search           : 0.00
% 13.06/5.98  Cooper               : 0.00
% 13.06/5.98  Total                : 5.20
% 13.06/5.98  Index Insertion      : 0.00
% 13.06/5.98  Index Deletion       : 0.00
% 13.06/5.98  Index Matching       : 0.00
% 13.06/5.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
