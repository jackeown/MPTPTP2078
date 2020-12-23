%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:31 EST 2020

% Result     : Theorem 15.73s
% Output     : CNFRefutation 15.73s
% Verified   : 
% Statistics : Number of formulae       :  182 (1038 expanded)
%              Number of leaves         :   42 ( 367 expanded)
%              Depth                    :   15
%              Number of atoms          :  426 (2870 expanded)
%              Number of equality atoms :   41 ( 297 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_94,plain,(
    ! [C_154,A_155,B_156] :
      ( v1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_94])).

tff(c_26660,plain,(
    ! [A_2141,B_2142,C_2143] :
      ( r2_hidden(k4_tarski('#skF_3'(A_2141,B_2142,C_2143),A_2141),C_2143)
      | ~ r2_hidden(A_2141,k9_relat_1(C_2143,B_2142))
      | ~ v1_relat_1(C_2143) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [A_219,B_220,C_221] :
      ( r2_hidden('#skF_3'(A_219,B_220,C_221),B_220)
      | ~ r2_hidden(A_219,k9_relat_1(C_221,B_220))
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_327,plain,(
    ! [B_222,A_223,C_224] :
      ( ~ v1_xboole_0(B_222)
      | ~ r2_hidden(A_223,k9_relat_1(C_224,B_222))
      | ~ v1_relat_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_314,c_2])).

tff(c_352,plain,(
    ! [B_222,C_224] :
      ( ~ v1_xboole_0(B_222)
      | ~ v1_relat_1(C_224)
      | v1_xboole_0(k9_relat_1(C_224,B_222)) ) ),
    inference(resolution,[status(thm)],[c_4,c_327])).

tff(c_406,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_relset_1(A_237,B_238,C_239,D_240) = k9_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_409,plain,(
    ! [D_240] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_240) = k9_relat_1('#skF_8',D_240) ),
    inference(resolution,[status(thm)],[c_64,c_406])).

tff(c_62,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_80,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_411,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_80])).

tff(c_424,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_352,c_411])).

tff(c_427,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_424])).

tff(c_412,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_62])).

tff(c_660,plain,(
    ! [A_276,B_277,C_278,D_279] :
      ( m1_subset_1(k7_relset_1(A_276,B_277,C_278,D_279),k1_zfmisc_1(B_277))
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_684,plain,(
    ! [D_240] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_240),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_660])).

tff(c_693,plain,(
    ! [D_280] : m1_subset_1(k9_relat_1('#skF_8',D_280),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_684])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_697,plain,(
    ! [A_281,D_282] :
      ( m1_subset_1(A_281,'#skF_6')
      | ~ r2_hidden(A_281,k9_relat_1('#skF_8',D_282)) ) ),
    inference(resolution,[status(thm)],[c_693,c_18])).

tff(c_721,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_412,c_697])).

tff(c_207,plain,(
    ! [C_191,B_192,A_193] :
      ( v1_xboole_0(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(B_192,A_193)))
      | ~ v1_xboole_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_211,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_207])).

tff(c_212,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_139,plain,(
    ! [C_169,A_170,B_171] :
      ( v4_relat_1(C_169,A_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_143,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [C_180,B_181,A_182] :
      ( r2_hidden(C_180,B_181)
      | ~ r2_hidden(C_180,A_182)
      | ~ r1_tarski(A_182,B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_176,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_1'(A_183),B_184)
      | ~ r1_tarski(A_183,B_184)
      | v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_4,c_166])).

tff(c_189,plain,(
    ! [B_185,A_186] :
      ( ~ v1_xboole_0(B_185)
      | ~ r1_tarski(A_186,B_185)
      | v1_xboole_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_225,plain,(
    ! [A_195,B_196] :
      ( ~ v1_xboole_0(A_195)
      | v1_xboole_0(k1_relat_1(B_196))
      | ~ v4_relat_1(B_196,A_195)
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_22,c_189])).

tff(c_229,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_143,c_225])).

tff(c_233,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_229])).

tff(c_235,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_1967,plain,(
    ! [D_393,A_389,B_392,C_390,E_391] :
      ( r2_hidden('#skF_4'(A_389,C_390,E_391,B_392,D_393),B_392)
      | ~ r2_hidden(E_391,k7_relset_1(C_390,A_389,D_393,B_392))
      | ~ m1_subset_1(E_391,A_389)
      | ~ m1_subset_1(D_393,k1_zfmisc_1(k2_zfmisc_1(C_390,A_389)))
      | v1_xboole_0(C_390)
      | v1_xboole_0(B_392)
      | v1_xboole_0(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1974,plain,(
    ! [E_391,B_392] :
      ( r2_hidden('#skF_4'('#skF_6','#skF_5',E_391,B_392,'#skF_8'),B_392)
      | ~ r2_hidden(E_391,k7_relset_1('#skF_5','#skF_6','#skF_8',B_392))
      | ~ m1_subset_1(E_391,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_392)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_1967])).

tff(c_1980,plain,(
    ! [E_391,B_392] :
      ( r2_hidden('#skF_4'('#skF_6','#skF_5',E_391,B_392,'#skF_8'),B_392)
      | ~ r2_hidden(E_391,k9_relat_1('#skF_8',B_392))
      | ~ m1_subset_1(E_391,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_392)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_1974])).

tff(c_5529,plain,(
    ! [E_717,B_718] :
      ( r2_hidden('#skF_4'('#skF_6','#skF_5',E_717,B_718,'#skF_8'),B_718)
      | ~ r2_hidden(E_717,k9_relat_1('#skF_8',B_718))
      | ~ m1_subset_1(E_717,'#skF_6')
      | v1_xboole_0(B_718) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_235,c_1980])).

tff(c_60,plain,(
    ! [F_146] :
      ( k1_funct_1('#skF_8',F_146) != '#skF_9'
      | ~ r2_hidden(F_146,'#skF_7')
      | ~ m1_subset_1(F_146,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_5614,plain,(
    ! [E_717] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5',E_717,'#skF_7','#skF_8')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_5',E_717,'#skF_7','#skF_8'),'#skF_5')
      | ~ r2_hidden(E_717,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_717,'#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5529,c_60])).

tff(c_5699,plain,(
    ! [E_728] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5',E_728,'#skF_7','#skF_8')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_5',E_728,'#skF_7','#skF_8'),'#skF_5')
      | ~ r2_hidden(E_728,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_728,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_5614])).

tff(c_5746,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_412,c_5699])).

tff(c_5782,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_5746])).

tff(c_12705,plain,(
    ~ m1_subset_1('#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5782])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_3'(A_17,B_18,C_19),k1_relat_1(C_19))
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_834,plain,(
    ! [A_297,B_298,C_299] :
      ( r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299),A_297),C_299)
      | ~ r2_hidden(A_297,k9_relat_1(C_299,B_298))
      | ~ v1_relat_1(C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3459,plain,(
    ! [C_534,A_535,B_536] :
      ( k1_funct_1(C_534,'#skF_3'(A_535,B_536,C_534)) = A_535
      | ~ v1_funct_1(C_534)
      | ~ r2_hidden(A_535,k9_relat_1(C_534,B_536))
      | ~ v1_relat_1(C_534) ) ),
    inference(resolution,[status(thm)],[c_834,c_34])).

tff(c_3475,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_412,c_3459])).

tff(c_3498,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68,c_3475])).

tff(c_32,plain,(
    ! [A_23,C_25] :
      ( r2_hidden(k4_tarski(A_23,k1_funct_1(C_25,A_23)),C_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3507,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3498,c_32])).

tff(c_3511,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_68,c_3507])).

tff(c_3513,plain,(
    ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3511])).

tff(c_3516,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_3513])).

tff(c_3520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_412,c_3516])).

tff(c_3521,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3511])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3928,plain,(
    ! [B_556] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_556)
      | ~ r1_tarski('#skF_8',B_556) ) ),
    inference(resolution,[status(thm)],[c_3521,c_6])).

tff(c_36,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(A_23,k1_relat_1(C_25))
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4033,plain,(
    ! [B_556] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_556))
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556)
      | ~ r1_tarski('#skF_8',B_556) ) ),
    inference(resolution,[status(thm)],[c_3928,c_36])).

tff(c_3570,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_6)
      | ~ r1_tarski('#skF_8',B_6) ) ),
    inference(resolution,[status(thm)],[c_3521,c_6])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_3'(A_17,B_18,C_19),B_18)
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1463,plain,(
    ! [A_345,C_346,B_347,D_348] :
      ( r2_hidden(A_345,k9_relat_1(C_346,B_347))
      | ~ r2_hidden(D_348,B_347)
      | ~ r2_hidden(k4_tarski(D_348,A_345),C_346)
      | ~ r2_hidden(D_348,k1_relat_1(C_346))
      | ~ v1_relat_1(C_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6830,plain,(
    ! [A_834,A_836,C_835,B_837,C_838] :
      ( r2_hidden(A_834,k9_relat_1(C_838,B_837))
      | ~ r2_hidden(k4_tarski('#skF_3'(A_836,B_837,C_835),A_834),C_838)
      | ~ r2_hidden('#skF_3'(A_836,B_837,C_835),k1_relat_1(C_838))
      | ~ v1_relat_1(C_838)
      | ~ r2_hidden(A_836,k9_relat_1(C_835,B_837))
      | ~ v1_relat_1(C_835) ) ),
    inference(resolution,[status(thm)],[c_26,c_1463])).

tff(c_6840,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_9',k9_relat_1(B_6,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',B_6) ) ),
    inference(resolution,[status(thm)],[c_3570,c_6830])).

tff(c_12812,plain,(
    ! [B_1354] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1354,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1354))
      | ~ v1_relat_1(B_1354)
      | ~ r1_tarski('#skF_8',B_1354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_412,c_6840])).

tff(c_12840,plain,(
    ! [B_556] :
      ( r2_hidden('#skF_9',k9_relat_1(B_556,'#skF_7'))
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556)
      | ~ r1_tarski('#skF_8',B_556) ) ),
    inference(resolution,[status(thm)],[c_4033,c_12812])).

tff(c_1628,plain,(
    ! [C_360,A_359,E_361,D_363,B_362] :
      ( m1_subset_1('#skF_4'(A_359,C_360,E_361,B_362,D_363),C_360)
      | ~ r2_hidden(E_361,k7_relset_1(C_360,A_359,D_363,B_362))
      | ~ m1_subset_1(E_361,A_359)
      | ~ m1_subset_1(D_363,k1_zfmisc_1(k2_zfmisc_1(C_360,A_359)))
      | v1_xboole_0(C_360)
      | v1_xboole_0(B_362)
      | v1_xboole_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1638,plain,(
    ! [E_361,D_240] :
      ( m1_subset_1('#skF_4'('#skF_6','#skF_5',E_361,D_240,'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_361,k9_relat_1('#skF_8',D_240))
      | ~ m1_subset_1(E_361,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_240)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_1628])).

tff(c_1658,plain,(
    ! [E_361,D_240] :
      ( m1_subset_1('#skF_4'('#skF_6','#skF_5',E_361,D_240,'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_361,k9_relat_1('#skF_8',D_240))
      | ~ m1_subset_1(E_361,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_240)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1638])).

tff(c_16968,plain,(
    ! [E_1586,D_1587] :
      ( m1_subset_1('#skF_4'('#skF_6','#skF_5',E_1586,D_1587,'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_1586,k9_relat_1('#skF_8',D_1587))
      | ~ m1_subset_1(E_1586,'#skF_6')
      | v1_xboole_0(D_1587) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_235,c_1658])).

tff(c_16996,plain,
    ( m1_subset_1('#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_12840,c_16968])).

tff(c_17105,plain,
    ( m1_subset_1('#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_98,c_68,c_721,c_16996])).

tff(c_17107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_12705,c_17105])).

tff(c_17108,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5782])).

tff(c_17183,plain,(
    ! [B_1595] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1595,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1595))
      | ~ v1_relat_1(B_1595)
      | ~ r1_tarski('#skF_8',B_1595) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_412,c_6840])).

tff(c_17211,plain,(
    ! [B_556] :
      ( r2_hidden('#skF_9',k9_relat_1(B_556,'#skF_7'))
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556)
      | ~ r1_tarski('#skF_8',B_556) ) ),
    inference(resolution,[status(thm)],[c_4033,c_17183])).

tff(c_2310,plain,(
    ! [C_423,E_424,B_425,D_426,A_422] :
      ( r2_hidden(k4_tarski('#skF_4'(A_422,C_423,E_424,B_425,D_426),E_424),D_426)
      | ~ r2_hidden(E_424,k7_relset_1(C_423,A_422,D_426,B_425))
      | ~ m1_subset_1(E_424,A_422)
      | ~ m1_subset_1(D_426,k1_zfmisc_1(k2_zfmisc_1(C_423,A_422)))
      | v1_xboole_0(C_423)
      | v1_xboole_0(B_425)
      | v1_xboole_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8566,plain,(
    ! [A_1020,E_1018,C_1021,D_1022,B_1019] :
      ( k1_funct_1(D_1022,'#skF_4'(A_1020,C_1021,E_1018,B_1019,D_1022)) = E_1018
      | ~ v1_funct_1(D_1022)
      | ~ v1_relat_1(D_1022)
      | ~ r2_hidden(E_1018,k7_relset_1(C_1021,A_1020,D_1022,B_1019))
      | ~ m1_subset_1(E_1018,A_1020)
      | ~ m1_subset_1(D_1022,k1_zfmisc_1(k2_zfmisc_1(C_1021,A_1020)))
      | v1_xboole_0(C_1021)
      | v1_xboole_0(B_1019)
      | v1_xboole_0(A_1020) ) ),
    inference(resolution,[status(thm)],[c_2310,c_34])).

tff(c_8612,plain,(
    ! [E_1018,D_240] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5',E_1018,D_240,'#skF_8')) = E_1018
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(E_1018,k9_relat_1('#skF_8',D_240))
      | ~ m1_subset_1(E_1018,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_240)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_8566])).

tff(c_8646,plain,(
    ! [E_1018,D_240] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5',E_1018,D_240,'#skF_8')) = E_1018
      | ~ r2_hidden(E_1018,k9_relat_1('#skF_8',D_240))
      | ~ m1_subset_1(E_1018,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_240)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_98,c_68,c_8612])).

tff(c_25212,plain,(
    ! [E_1991,D_1992] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5',E_1991,D_1992,'#skF_8')) = E_1991
      | ~ r2_hidden(E_1991,k9_relat_1('#skF_8',D_1992))
      | ~ m1_subset_1(E_1991,'#skF_6')
      | v1_xboole_0(D_1992) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_235,c_8646])).

tff(c_25244,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_17211,c_25212])).

tff(c_25356,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_6','#skF_5','#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_98,c_68,c_721,c_25244])).

tff(c_25358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_17108,c_25356])).

tff(c_25360,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_25555,plain,(
    ! [A_2018,B_2019,C_2020] :
      ( r2_hidden('#skF_3'(A_2018,B_2019,C_2020),B_2019)
      | ~ r2_hidden(A_2018,k9_relat_1(C_2020,B_2019))
      | ~ v1_relat_1(C_2020) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25568,plain,(
    ! [B_2021,A_2022,C_2023] :
      ( ~ v1_xboole_0(B_2021)
      | ~ r2_hidden(A_2022,k9_relat_1(C_2023,B_2021))
      | ~ v1_relat_1(C_2023) ) ),
    inference(resolution,[status(thm)],[c_25555,c_2])).

tff(c_25594,plain,(
    ! [B_2024,C_2025] :
      ( ~ v1_xboole_0(B_2024)
      | ~ v1_relat_1(C_2025)
      | v1_xboole_0(k9_relat_1(C_2025,B_2024)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25568])).

tff(c_99,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_2'(A_157,B_158),A_157)
      | r1_tarski(A_157,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_157,B_158] :
      ( ~ v1_xboole_0(A_157)
      | r1_tarski(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_109,plain,(
    ! [A_159,B_160] :
      ( ~ v1_xboole_0(A_159)
      | r1_tarski(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [B_161,A_162] :
      ( B_161 = A_162
      | ~ r1_tarski(B_161,A_162)
      | ~ v1_xboole_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_109,c_12])).

tff(c_120,plain,(
    ! [B_158,A_157] :
      ( B_158 = A_157
      | ~ v1_xboole_0(B_158)
      | ~ v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_108,c_113])).

tff(c_25363,plain,(
    ! [A_157] :
      ( A_157 = '#skF_5'
      | ~ v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_25360,c_120])).

tff(c_25602,plain,(
    ! [C_2026,B_2027] :
      ( k9_relat_1(C_2026,B_2027) = '#skF_5'
      | ~ v1_xboole_0(B_2027)
      | ~ v1_relat_1(C_2026) ) ),
    inference(resolution,[status(thm)],[c_25594,c_25363])).

tff(c_25610,plain,(
    ! [C_2029] :
      ( k9_relat_1(C_2029,'#skF_5') = '#skF_5'
      | ~ v1_relat_1(C_2029) ) ),
    inference(resolution,[status(thm)],[c_25360,c_25602])).

tff(c_25614,plain,(
    k9_relat_1('#skF_8','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_98,c_25610])).

tff(c_25567,plain,(
    ! [B_2019,A_2018,C_2020] :
      ( ~ v1_xboole_0(B_2019)
      | ~ r2_hidden(A_2018,k9_relat_1(C_2020,B_2019))
      | ~ v1_relat_1(C_2020) ) ),
    inference(resolution,[status(thm)],[c_25555,c_2])).

tff(c_25621,plain,(
    ! [A_2018] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_2018,'#skF_5')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25614,c_25567])).

tff(c_25627,plain,(
    ! [A_2018] : ~ r2_hidden(A_2018,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_25360,c_25621])).

tff(c_25359,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_25380,plain,(
    ! [A_1994] :
      ( A_1994 = '#skF_5'
      | ~ v1_xboole_0(A_1994) ) ),
    inference(resolution,[status(thm)],[c_25360,c_120])).

tff(c_25387,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_25359,c_25380])).

tff(c_25949,plain,(
    ! [A_2059,B_2060,C_2061] :
      ( r2_hidden('#skF_3'(A_2059,B_2060,C_2061),k1_relat_1(C_2061))
      | ~ r2_hidden(A_2059,k9_relat_1(C_2061,B_2060))
      | ~ v1_relat_1(C_2061) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25957,plain,(
    ! [A_2059,B_2060] :
      ( r2_hidden('#skF_3'(A_2059,B_2060,'#skF_8'),'#skF_5')
      | ~ r2_hidden(A_2059,k9_relat_1('#skF_8',B_2060))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25387,c_25949])).

tff(c_25961,plain,(
    ! [A_2059,B_2060] :
      ( r2_hidden('#skF_3'(A_2059,B_2060,'#skF_8'),'#skF_5')
      | ~ r2_hidden(A_2059,k9_relat_1('#skF_8',B_2060)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_25957])).

tff(c_25962,plain,(
    ! [A_2059,B_2060] : ~ r2_hidden(A_2059,k9_relat_1('#skF_8',B_2060)) ),
    inference(negUnitSimplification,[status(thm)],[c_25627,c_25961])).

tff(c_25699,plain,(
    ! [A_2034,B_2035,C_2036,D_2037] :
      ( k7_relset_1(A_2034,B_2035,C_2036,D_2037) = k9_relat_1(C_2036,D_2037)
      | ~ m1_subset_1(C_2036,k1_zfmisc_1(k2_zfmisc_1(A_2034,B_2035))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_25702,plain,(
    ! [D_2037] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_2037) = k9_relat_1('#skF_8',D_2037) ),
    inference(resolution,[status(thm)],[c_64,c_25699])).

tff(c_25794,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25702,c_62])).

tff(c_25964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25962,c_25794])).

tff(c_25965,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_26053,plain,(
    ! [A_2070,B_2071,C_2072] :
      ( r2_hidden('#skF_3'(A_2070,B_2071,C_2072),B_2071)
      | ~ r2_hidden(A_2070,k9_relat_1(C_2072,B_2071))
      | ~ v1_relat_1(C_2072) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26066,plain,(
    ! [B_2073,A_2074,C_2075] :
      ( ~ v1_xboole_0(B_2073)
      | ~ r2_hidden(A_2074,k9_relat_1(C_2075,B_2073))
      | ~ v1_relat_1(C_2075) ) ),
    inference(resolution,[status(thm)],[c_26053,c_2])).

tff(c_26087,plain,(
    ! [B_2076,C_2077] :
      ( ~ v1_xboole_0(B_2076)
      | ~ v1_relat_1(C_2077)
      | v1_xboole_0(k9_relat_1(C_2077,B_2076)) ) ),
    inference(resolution,[status(thm)],[c_4,c_26066])).

tff(c_25969,plain,(
    ! [A_157] :
      ( A_157 = '#skF_8'
      | ~ v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_25965,c_120])).

tff(c_26096,plain,(
    ! [C_2079,B_2080] :
      ( k9_relat_1(C_2079,B_2080) = '#skF_8'
      | ~ v1_xboole_0(B_2080)
      | ~ v1_relat_1(C_2079) ) ),
    inference(resolution,[status(thm)],[c_26087,c_25969])).

tff(c_26103,plain,(
    ! [C_2081] :
      ( k9_relat_1(C_2081,'#skF_8') = '#skF_8'
      | ~ v1_relat_1(C_2081) ) ),
    inference(resolution,[status(thm)],[c_25965,c_26096])).

tff(c_26107,plain,(
    k9_relat_1('#skF_8','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_98,c_26103])).

tff(c_26065,plain,(
    ! [B_2071,A_2070,C_2072] :
      ( ~ v1_xboole_0(B_2071)
      | ~ r2_hidden(A_2070,k9_relat_1(C_2072,B_2071))
      | ~ v1_relat_1(C_2072) ) ),
    inference(resolution,[status(thm)],[c_26053,c_2])).

tff(c_26114,plain,(
    ! [A_2070] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_2070,'#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26107,c_26065])).

tff(c_26120,plain,(
    ! [A_2070] : ~ r2_hidden(A_2070,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_25965,c_26114])).

tff(c_26683,plain,(
    ! [A_2141,B_2142] :
      ( ~ r2_hidden(A_2141,k9_relat_1('#skF_8',B_2142))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_26660,c_26120])).

tff(c_26707,plain,(
    ! [A_2141,B_2142] : ~ r2_hidden(A_2141,k9_relat_1('#skF_8',B_2142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_26683])).

tff(c_25966,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_25985,plain,(
    ! [A_2063] :
      ( A_2063 = '#skF_8'
      | ~ v1_xboole_0(A_2063) ) ),
    inference(resolution,[status(thm)],[c_25965,c_120])).

tff(c_25992,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_25966,c_25985])).

tff(c_26001,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25992,c_64])).

tff(c_26445,plain,(
    ! [A_2118,B_2119,C_2120,D_2121] :
      ( k7_relset_1(A_2118,B_2119,C_2120,D_2121) = k9_relat_1(C_2120,D_2121)
      | ~ m1_subset_1(C_2120,k1_zfmisc_1(k2_zfmisc_1(A_2118,B_2119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26448,plain,(
    ! [D_2121] : k7_relset_1('#skF_5','#skF_8','#skF_8',D_2121) = k9_relat_1('#skF_8',D_2121) ),
    inference(resolution,[status(thm)],[c_26001,c_26445])).

tff(c_26000,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_8','#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25992,c_62])).

tff(c_26449,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26448,c_26000])).

tff(c_26714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26707,c_26449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.73/7.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.73/7.38  
% 15.73/7.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.73/7.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 15.73/7.38  
% 15.73/7.38  %Foreground sorts:
% 15.73/7.38  
% 15.73/7.38  
% 15.73/7.38  %Background operators:
% 15.73/7.38  
% 15.73/7.38  
% 15.73/7.38  %Foreground operators:
% 15.73/7.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.73/7.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.73/7.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.73/7.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.73/7.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.73/7.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 15.73/7.38  tff('#skF_7', type, '#skF_7': $i).
% 15.73/7.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.73/7.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 15.73/7.38  tff('#skF_5', type, '#skF_5': $i).
% 15.73/7.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.73/7.38  tff('#skF_6', type, '#skF_6': $i).
% 15.73/7.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.73/7.38  tff('#skF_9', type, '#skF_9': $i).
% 15.73/7.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.73/7.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.73/7.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.73/7.38  tff('#skF_8', type, '#skF_8': $i).
% 15.73/7.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.73/7.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.73/7.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.73/7.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.73/7.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.73/7.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.73/7.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.73/7.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.73/7.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.73/7.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.73/7.38  
% 15.73/7.40  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 15.73/7.40  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.73/7.40  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 15.73/7.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.73/7.40  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 15.73/7.40  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 15.73/7.40  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 15.73/7.40  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 15.73/7.40  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.73/7.40  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 15.73/7.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.73/7.40  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 15.73/7.40  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.73/7.40  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 15.73/7.40  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.73/7.40  tff(c_94, plain, (![C_154, A_155, B_156]: (v1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.73/7.40  tff(c_98, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_94])).
% 15.73/7.40  tff(c_26660, plain, (![A_2141, B_2142, C_2143]: (r2_hidden(k4_tarski('#skF_3'(A_2141, B_2142, C_2143), A_2141), C_2143) | ~r2_hidden(A_2141, k9_relat_1(C_2143, B_2142)) | ~v1_relat_1(C_2143))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.73/7.40  tff(c_314, plain, (![A_219, B_220, C_221]: (r2_hidden('#skF_3'(A_219, B_220, C_221), B_220) | ~r2_hidden(A_219, k9_relat_1(C_221, B_220)) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.73/7.40  tff(c_327, plain, (![B_222, A_223, C_224]: (~v1_xboole_0(B_222) | ~r2_hidden(A_223, k9_relat_1(C_224, B_222)) | ~v1_relat_1(C_224))), inference(resolution, [status(thm)], [c_314, c_2])).
% 15.73/7.40  tff(c_352, plain, (![B_222, C_224]: (~v1_xboole_0(B_222) | ~v1_relat_1(C_224) | v1_xboole_0(k9_relat_1(C_224, B_222)))), inference(resolution, [status(thm)], [c_4, c_327])).
% 15.73/7.40  tff(c_406, plain, (![A_237, B_238, C_239, D_240]: (k7_relset_1(A_237, B_238, C_239, D_240)=k9_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.73/7.40  tff(c_409, plain, (![D_240]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_240)=k9_relat_1('#skF_8', D_240))), inference(resolution, [status(thm)], [c_64, c_406])).
% 15.73/7.40  tff(c_62, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.73/7.40  tff(c_80, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_2])).
% 15.73/7.40  tff(c_411, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_80])).
% 15.73/7.40  tff(c_424, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_352, c_411])).
% 15.73/7.40  tff(c_427, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_424])).
% 15.73/7.40  tff(c_412, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_62])).
% 15.73/7.40  tff(c_660, plain, (![A_276, B_277, C_278, D_279]: (m1_subset_1(k7_relset_1(A_276, B_277, C_278, D_279), k1_zfmisc_1(B_277)) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.73/7.40  tff(c_684, plain, (![D_240]: (m1_subset_1(k9_relat_1('#skF_8', D_240), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_409, c_660])).
% 15.73/7.40  tff(c_693, plain, (![D_280]: (m1_subset_1(k9_relat_1('#skF_8', D_280), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_684])).
% 15.73/7.40  tff(c_18, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.73/7.40  tff(c_697, plain, (![A_281, D_282]: (m1_subset_1(A_281, '#skF_6') | ~r2_hidden(A_281, k9_relat_1('#skF_8', D_282)))), inference(resolution, [status(thm)], [c_693, c_18])).
% 15.73/7.40  tff(c_721, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_412, c_697])).
% 15.73/7.40  tff(c_207, plain, (![C_191, B_192, A_193]: (v1_xboole_0(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(B_192, A_193))) | ~v1_xboole_0(A_193))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.73/7.40  tff(c_211, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_207])).
% 15.73/7.40  tff(c_212, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_211])).
% 15.73/7.40  tff(c_139, plain, (![C_169, A_170, B_171]: (v4_relat_1(C_169, A_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.73/7.40  tff(c_143, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_139])).
% 15.73/7.40  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.73/7.40  tff(c_166, plain, (![C_180, B_181, A_182]: (r2_hidden(C_180, B_181) | ~r2_hidden(C_180, A_182) | ~r1_tarski(A_182, B_181))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.73/7.40  tff(c_176, plain, (![A_183, B_184]: (r2_hidden('#skF_1'(A_183), B_184) | ~r1_tarski(A_183, B_184) | v1_xboole_0(A_183))), inference(resolution, [status(thm)], [c_4, c_166])).
% 15.73/7.40  tff(c_189, plain, (![B_185, A_186]: (~v1_xboole_0(B_185) | ~r1_tarski(A_186, B_185) | v1_xboole_0(A_186))), inference(resolution, [status(thm)], [c_176, c_2])).
% 15.73/7.40  tff(c_225, plain, (![A_195, B_196]: (~v1_xboole_0(A_195) | v1_xboole_0(k1_relat_1(B_196)) | ~v4_relat_1(B_196, A_195) | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_22, c_189])).
% 15.73/7.40  tff(c_229, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_143, c_225])).
% 15.73/7.40  tff(c_233, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_229])).
% 15.73/7.40  tff(c_235, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_233])).
% 15.73/7.40  tff(c_1967, plain, (![D_393, A_389, B_392, C_390, E_391]: (r2_hidden('#skF_4'(A_389, C_390, E_391, B_392, D_393), B_392) | ~r2_hidden(E_391, k7_relset_1(C_390, A_389, D_393, B_392)) | ~m1_subset_1(E_391, A_389) | ~m1_subset_1(D_393, k1_zfmisc_1(k2_zfmisc_1(C_390, A_389))) | v1_xboole_0(C_390) | v1_xboole_0(B_392) | v1_xboole_0(A_389))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.73/7.40  tff(c_1974, plain, (![E_391, B_392]: (r2_hidden('#skF_4'('#skF_6', '#skF_5', E_391, B_392, '#skF_8'), B_392) | ~r2_hidden(E_391, k7_relset_1('#skF_5', '#skF_6', '#skF_8', B_392)) | ~m1_subset_1(E_391, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_392) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_1967])).
% 15.73/7.40  tff(c_1980, plain, (![E_391, B_392]: (r2_hidden('#skF_4'('#skF_6', '#skF_5', E_391, B_392, '#skF_8'), B_392) | ~r2_hidden(E_391, k9_relat_1('#skF_8', B_392)) | ~m1_subset_1(E_391, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_392) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_1974])).
% 15.73/7.40  tff(c_5529, plain, (![E_717, B_718]: (r2_hidden('#skF_4'('#skF_6', '#skF_5', E_717, B_718, '#skF_8'), B_718) | ~r2_hidden(E_717, k9_relat_1('#skF_8', B_718)) | ~m1_subset_1(E_717, '#skF_6') | v1_xboole_0(B_718))), inference(negUnitSimplification, [status(thm)], [c_212, c_235, c_1980])).
% 15.73/7.40  tff(c_60, plain, (![F_146]: (k1_funct_1('#skF_8', F_146)!='#skF_9' | ~r2_hidden(F_146, '#skF_7') | ~m1_subset_1(F_146, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.73/7.40  tff(c_5614, plain, (![E_717]: (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', E_717, '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_6', '#skF_5', E_717, '#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden(E_717, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_717, '#skF_6') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_5529, c_60])).
% 15.73/7.40  tff(c_5699, plain, (![E_728]: (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', E_728, '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_6', '#skF_5', E_728, '#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden(E_728, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_728, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_427, c_5614])).
% 15.73/7.40  tff(c_5746, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_412, c_5699])).
% 15.73/7.40  tff(c_5782, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_721, c_5746])).
% 15.73/7.40  tff(c_12705, plain, (~m1_subset_1('#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5782])).
% 15.73/7.40  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.73/7.40  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.73/7.40  tff(c_30, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_3'(A_17, B_18, C_19), k1_relat_1(C_19)) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_834, plain, (![A_297, B_298, C_299]: (r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299), A_297), C_299) | ~r2_hidden(A_297, k9_relat_1(C_299, B_298)) | ~v1_relat_1(C_299))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_34, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.73/7.40  tff(c_3459, plain, (![C_534, A_535, B_536]: (k1_funct_1(C_534, '#skF_3'(A_535, B_536, C_534))=A_535 | ~v1_funct_1(C_534) | ~r2_hidden(A_535, k9_relat_1(C_534, B_536)) | ~v1_relat_1(C_534))), inference(resolution, [status(thm)], [c_834, c_34])).
% 15.73/7.40  tff(c_3475, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_412, c_3459])).
% 15.73/7.40  tff(c_3498, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_68, c_3475])).
% 15.73/7.40  tff(c_32, plain, (![A_23, C_25]: (r2_hidden(k4_tarski(A_23, k1_funct_1(C_25, A_23)), C_25) | ~r2_hidden(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.73/7.40  tff(c_3507, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3498, c_32])).
% 15.73/7.40  tff(c_3511, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_68, c_3507])).
% 15.73/7.40  tff(c_3513, plain, (~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3511])).
% 15.73/7.40  tff(c_3516, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_30, c_3513])).
% 15.73/7.40  tff(c_3520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_412, c_3516])).
% 15.73/7.40  tff(c_3521, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_3511])).
% 15.73/7.40  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.73/7.40  tff(c_3928, plain, (![B_556]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_556) | ~r1_tarski('#skF_8', B_556))), inference(resolution, [status(thm)], [c_3521, c_6])).
% 15.73/7.40  tff(c_36, plain, (![A_23, C_25, B_24]: (r2_hidden(A_23, k1_relat_1(C_25)) | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.73/7.40  tff(c_4033, plain, (![B_556]: (r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_556)) | ~v1_funct_1(B_556) | ~v1_relat_1(B_556) | ~r1_tarski('#skF_8', B_556))), inference(resolution, [status(thm)], [c_3928, c_36])).
% 15.73/7.40  tff(c_3570, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_6) | ~r1_tarski('#skF_8', B_6))), inference(resolution, [status(thm)], [c_3521, c_6])).
% 15.73/7.40  tff(c_26, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_3'(A_17, B_18, C_19), B_18) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_1463, plain, (![A_345, C_346, B_347, D_348]: (r2_hidden(A_345, k9_relat_1(C_346, B_347)) | ~r2_hidden(D_348, B_347) | ~r2_hidden(k4_tarski(D_348, A_345), C_346) | ~r2_hidden(D_348, k1_relat_1(C_346)) | ~v1_relat_1(C_346))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_6830, plain, (![A_834, A_836, C_835, B_837, C_838]: (r2_hidden(A_834, k9_relat_1(C_838, B_837)) | ~r2_hidden(k4_tarski('#skF_3'(A_836, B_837, C_835), A_834), C_838) | ~r2_hidden('#skF_3'(A_836, B_837, C_835), k1_relat_1(C_838)) | ~v1_relat_1(C_838) | ~r2_hidden(A_836, k9_relat_1(C_835, B_837)) | ~v1_relat_1(C_835))), inference(resolution, [status(thm)], [c_26, c_1463])).
% 15.73/7.40  tff(c_6840, plain, (![B_6]: (r2_hidden('#skF_9', k9_relat_1(B_6, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_6)) | ~v1_relat_1(B_6) | ~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', B_6))), inference(resolution, [status(thm)], [c_3570, c_6830])).
% 15.73/7.40  tff(c_12812, plain, (![B_1354]: (r2_hidden('#skF_9', k9_relat_1(B_1354, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1354)) | ~v1_relat_1(B_1354) | ~r1_tarski('#skF_8', B_1354))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_412, c_6840])).
% 15.73/7.40  tff(c_12840, plain, (![B_556]: (r2_hidden('#skF_9', k9_relat_1(B_556, '#skF_7')) | ~v1_funct_1(B_556) | ~v1_relat_1(B_556) | ~r1_tarski('#skF_8', B_556))), inference(resolution, [status(thm)], [c_4033, c_12812])).
% 15.73/7.40  tff(c_1628, plain, (![C_360, A_359, E_361, D_363, B_362]: (m1_subset_1('#skF_4'(A_359, C_360, E_361, B_362, D_363), C_360) | ~r2_hidden(E_361, k7_relset_1(C_360, A_359, D_363, B_362)) | ~m1_subset_1(E_361, A_359) | ~m1_subset_1(D_363, k1_zfmisc_1(k2_zfmisc_1(C_360, A_359))) | v1_xboole_0(C_360) | v1_xboole_0(B_362) | v1_xboole_0(A_359))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.73/7.40  tff(c_1638, plain, (![E_361, D_240]: (m1_subset_1('#skF_4'('#skF_6', '#skF_5', E_361, D_240, '#skF_8'), '#skF_5') | ~r2_hidden(E_361, k9_relat_1('#skF_8', D_240)) | ~m1_subset_1(E_361, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_240) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_1628])).
% 15.73/7.40  tff(c_1658, plain, (![E_361, D_240]: (m1_subset_1('#skF_4'('#skF_6', '#skF_5', E_361, D_240, '#skF_8'), '#skF_5') | ~r2_hidden(E_361, k9_relat_1('#skF_8', D_240)) | ~m1_subset_1(E_361, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_240) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1638])).
% 15.73/7.40  tff(c_16968, plain, (![E_1586, D_1587]: (m1_subset_1('#skF_4'('#skF_6', '#skF_5', E_1586, D_1587, '#skF_8'), '#skF_5') | ~r2_hidden(E_1586, k9_relat_1('#skF_8', D_1587)) | ~m1_subset_1(E_1586, '#skF_6') | v1_xboole_0(D_1587))), inference(negUnitSimplification, [status(thm)], [c_212, c_235, c_1658])).
% 15.73/7.40  tff(c_16996, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_12840, c_16968])).
% 15.73/7.40  tff(c_17105, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'), '#skF_5') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_98, c_68, c_721, c_16996])).
% 15.73/7.40  tff(c_17107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_12705, c_17105])).
% 15.73/7.40  tff(c_17108, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(splitRight, [status(thm)], [c_5782])).
% 15.73/7.40  tff(c_17183, plain, (![B_1595]: (r2_hidden('#skF_9', k9_relat_1(B_1595, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1595)) | ~v1_relat_1(B_1595) | ~r1_tarski('#skF_8', B_1595))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_412, c_6840])).
% 15.73/7.40  tff(c_17211, plain, (![B_556]: (r2_hidden('#skF_9', k9_relat_1(B_556, '#skF_7')) | ~v1_funct_1(B_556) | ~v1_relat_1(B_556) | ~r1_tarski('#skF_8', B_556))), inference(resolution, [status(thm)], [c_4033, c_17183])).
% 15.73/7.40  tff(c_2310, plain, (![C_423, E_424, B_425, D_426, A_422]: (r2_hidden(k4_tarski('#skF_4'(A_422, C_423, E_424, B_425, D_426), E_424), D_426) | ~r2_hidden(E_424, k7_relset_1(C_423, A_422, D_426, B_425)) | ~m1_subset_1(E_424, A_422) | ~m1_subset_1(D_426, k1_zfmisc_1(k2_zfmisc_1(C_423, A_422))) | v1_xboole_0(C_423) | v1_xboole_0(B_425) | v1_xboole_0(A_422))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.73/7.40  tff(c_8566, plain, (![A_1020, E_1018, C_1021, D_1022, B_1019]: (k1_funct_1(D_1022, '#skF_4'(A_1020, C_1021, E_1018, B_1019, D_1022))=E_1018 | ~v1_funct_1(D_1022) | ~v1_relat_1(D_1022) | ~r2_hidden(E_1018, k7_relset_1(C_1021, A_1020, D_1022, B_1019)) | ~m1_subset_1(E_1018, A_1020) | ~m1_subset_1(D_1022, k1_zfmisc_1(k2_zfmisc_1(C_1021, A_1020))) | v1_xboole_0(C_1021) | v1_xboole_0(B_1019) | v1_xboole_0(A_1020))), inference(resolution, [status(thm)], [c_2310, c_34])).
% 15.73/7.40  tff(c_8612, plain, (![E_1018, D_240]: (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', E_1018, D_240, '#skF_8'))=E_1018 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(E_1018, k9_relat_1('#skF_8', D_240)) | ~m1_subset_1(E_1018, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_240) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_8566])).
% 15.73/7.40  tff(c_8646, plain, (![E_1018, D_240]: (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', E_1018, D_240, '#skF_8'))=E_1018 | ~r2_hidden(E_1018, k9_relat_1('#skF_8', D_240)) | ~m1_subset_1(E_1018, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_240) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_98, c_68, c_8612])).
% 15.73/7.40  tff(c_25212, plain, (![E_1991, D_1992]: (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', E_1991, D_1992, '#skF_8'))=E_1991 | ~r2_hidden(E_1991, k9_relat_1('#skF_8', D_1992)) | ~m1_subset_1(E_1991, '#skF_6') | v1_xboole_0(D_1992))), inference(negUnitSimplification, [status(thm)], [c_212, c_235, c_8646])).
% 15.73/7.40  tff(c_25244, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_17211, c_25212])).
% 15.73/7.40  tff(c_25356, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_6', '#skF_5', '#skF_9', '#skF_7', '#skF_8'))='#skF_9' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_98, c_68, c_721, c_25244])).
% 15.73/7.40  tff(c_25358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_17108, c_25356])).
% 15.73/7.40  tff(c_25360, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_233])).
% 15.73/7.40  tff(c_25555, plain, (![A_2018, B_2019, C_2020]: (r2_hidden('#skF_3'(A_2018, B_2019, C_2020), B_2019) | ~r2_hidden(A_2018, k9_relat_1(C_2020, B_2019)) | ~v1_relat_1(C_2020))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_25568, plain, (![B_2021, A_2022, C_2023]: (~v1_xboole_0(B_2021) | ~r2_hidden(A_2022, k9_relat_1(C_2023, B_2021)) | ~v1_relat_1(C_2023))), inference(resolution, [status(thm)], [c_25555, c_2])).
% 15.73/7.40  tff(c_25594, plain, (![B_2024, C_2025]: (~v1_xboole_0(B_2024) | ~v1_relat_1(C_2025) | v1_xboole_0(k9_relat_1(C_2025, B_2024)))), inference(resolution, [status(thm)], [c_4, c_25568])).
% 15.73/7.40  tff(c_99, plain, (![A_157, B_158]: (r2_hidden('#skF_2'(A_157, B_158), A_157) | r1_tarski(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.73/7.40  tff(c_108, plain, (![A_157, B_158]: (~v1_xboole_0(A_157) | r1_tarski(A_157, B_158))), inference(resolution, [status(thm)], [c_99, c_2])).
% 15.73/7.40  tff(c_109, plain, (![A_159, B_160]: (~v1_xboole_0(A_159) | r1_tarski(A_159, B_160))), inference(resolution, [status(thm)], [c_99, c_2])).
% 15.73/7.40  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.73/7.40  tff(c_113, plain, (![B_161, A_162]: (B_161=A_162 | ~r1_tarski(B_161, A_162) | ~v1_xboole_0(A_162))), inference(resolution, [status(thm)], [c_109, c_12])).
% 15.73/7.40  tff(c_120, plain, (![B_158, A_157]: (B_158=A_157 | ~v1_xboole_0(B_158) | ~v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_108, c_113])).
% 15.73/7.40  tff(c_25363, plain, (![A_157]: (A_157='#skF_5' | ~v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_25360, c_120])).
% 15.73/7.40  tff(c_25602, plain, (![C_2026, B_2027]: (k9_relat_1(C_2026, B_2027)='#skF_5' | ~v1_xboole_0(B_2027) | ~v1_relat_1(C_2026))), inference(resolution, [status(thm)], [c_25594, c_25363])).
% 15.73/7.40  tff(c_25610, plain, (![C_2029]: (k9_relat_1(C_2029, '#skF_5')='#skF_5' | ~v1_relat_1(C_2029))), inference(resolution, [status(thm)], [c_25360, c_25602])).
% 15.73/7.40  tff(c_25614, plain, (k9_relat_1('#skF_8', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_98, c_25610])).
% 15.73/7.40  tff(c_25567, plain, (![B_2019, A_2018, C_2020]: (~v1_xboole_0(B_2019) | ~r2_hidden(A_2018, k9_relat_1(C_2020, B_2019)) | ~v1_relat_1(C_2020))), inference(resolution, [status(thm)], [c_25555, c_2])).
% 15.73/7.40  tff(c_25621, plain, (![A_2018]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_2018, '#skF_5') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_25614, c_25567])).
% 15.73/7.40  tff(c_25627, plain, (![A_2018]: (~r2_hidden(A_2018, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_25360, c_25621])).
% 15.73/7.40  tff(c_25359, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_233])).
% 15.73/7.40  tff(c_25380, plain, (![A_1994]: (A_1994='#skF_5' | ~v1_xboole_0(A_1994))), inference(resolution, [status(thm)], [c_25360, c_120])).
% 15.73/7.40  tff(c_25387, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(resolution, [status(thm)], [c_25359, c_25380])).
% 15.73/7.40  tff(c_25949, plain, (![A_2059, B_2060, C_2061]: (r2_hidden('#skF_3'(A_2059, B_2060, C_2061), k1_relat_1(C_2061)) | ~r2_hidden(A_2059, k9_relat_1(C_2061, B_2060)) | ~v1_relat_1(C_2061))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_25957, plain, (![A_2059, B_2060]: (r2_hidden('#skF_3'(A_2059, B_2060, '#skF_8'), '#skF_5') | ~r2_hidden(A_2059, k9_relat_1('#skF_8', B_2060)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_25387, c_25949])).
% 15.73/7.40  tff(c_25961, plain, (![A_2059, B_2060]: (r2_hidden('#skF_3'(A_2059, B_2060, '#skF_8'), '#skF_5') | ~r2_hidden(A_2059, k9_relat_1('#skF_8', B_2060)))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_25957])).
% 15.73/7.40  tff(c_25962, plain, (![A_2059, B_2060]: (~r2_hidden(A_2059, k9_relat_1('#skF_8', B_2060)))), inference(negUnitSimplification, [status(thm)], [c_25627, c_25961])).
% 15.73/7.40  tff(c_25699, plain, (![A_2034, B_2035, C_2036, D_2037]: (k7_relset_1(A_2034, B_2035, C_2036, D_2037)=k9_relat_1(C_2036, D_2037) | ~m1_subset_1(C_2036, k1_zfmisc_1(k2_zfmisc_1(A_2034, B_2035))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.73/7.40  tff(c_25702, plain, (![D_2037]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_2037)=k9_relat_1('#skF_8', D_2037))), inference(resolution, [status(thm)], [c_64, c_25699])).
% 15.73/7.40  tff(c_25794, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_25702, c_62])).
% 15.73/7.40  tff(c_25964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25962, c_25794])).
% 15.73/7.40  tff(c_25965, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_211])).
% 15.73/7.40  tff(c_26053, plain, (![A_2070, B_2071, C_2072]: (r2_hidden('#skF_3'(A_2070, B_2071, C_2072), B_2071) | ~r2_hidden(A_2070, k9_relat_1(C_2072, B_2071)) | ~v1_relat_1(C_2072))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.73/7.40  tff(c_26066, plain, (![B_2073, A_2074, C_2075]: (~v1_xboole_0(B_2073) | ~r2_hidden(A_2074, k9_relat_1(C_2075, B_2073)) | ~v1_relat_1(C_2075))), inference(resolution, [status(thm)], [c_26053, c_2])).
% 15.73/7.40  tff(c_26087, plain, (![B_2076, C_2077]: (~v1_xboole_0(B_2076) | ~v1_relat_1(C_2077) | v1_xboole_0(k9_relat_1(C_2077, B_2076)))), inference(resolution, [status(thm)], [c_4, c_26066])).
% 15.73/7.40  tff(c_25969, plain, (![A_157]: (A_157='#skF_8' | ~v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_25965, c_120])).
% 15.73/7.40  tff(c_26096, plain, (![C_2079, B_2080]: (k9_relat_1(C_2079, B_2080)='#skF_8' | ~v1_xboole_0(B_2080) | ~v1_relat_1(C_2079))), inference(resolution, [status(thm)], [c_26087, c_25969])).
% 15.73/7.40  tff(c_26103, plain, (![C_2081]: (k9_relat_1(C_2081, '#skF_8')='#skF_8' | ~v1_relat_1(C_2081))), inference(resolution, [status(thm)], [c_25965, c_26096])).
% 15.73/7.40  tff(c_26107, plain, (k9_relat_1('#skF_8', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_98, c_26103])).
% 15.73/7.40  tff(c_26065, plain, (![B_2071, A_2070, C_2072]: (~v1_xboole_0(B_2071) | ~r2_hidden(A_2070, k9_relat_1(C_2072, B_2071)) | ~v1_relat_1(C_2072))), inference(resolution, [status(thm)], [c_26053, c_2])).
% 15.73/7.40  tff(c_26114, plain, (![A_2070]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_2070, '#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_26107, c_26065])).
% 15.73/7.40  tff(c_26120, plain, (![A_2070]: (~r2_hidden(A_2070, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_25965, c_26114])).
% 15.73/7.40  tff(c_26683, plain, (![A_2141, B_2142]: (~r2_hidden(A_2141, k9_relat_1('#skF_8', B_2142)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_26660, c_26120])).
% 15.73/7.40  tff(c_26707, plain, (![A_2141, B_2142]: (~r2_hidden(A_2141, k9_relat_1('#skF_8', B_2142)))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_26683])).
% 15.73/7.40  tff(c_25966, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_211])).
% 15.73/7.40  tff(c_25985, plain, (![A_2063]: (A_2063='#skF_8' | ~v1_xboole_0(A_2063))), inference(resolution, [status(thm)], [c_25965, c_120])).
% 15.73/7.40  tff(c_25992, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_25966, c_25985])).
% 15.73/7.40  tff(c_26001, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_25992, c_64])).
% 15.73/7.40  tff(c_26445, plain, (![A_2118, B_2119, C_2120, D_2121]: (k7_relset_1(A_2118, B_2119, C_2120, D_2121)=k9_relat_1(C_2120, D_2121) | ~m1_subset_1(C_2120, k1_zfmisc_1(k2_zfmisc_1(A_2118, B_2119))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.73/7.40  tff(c_26448, plain, (![D_2121]: (k7_relset_1('#skF_5', '#skF_8', '#skF_8', D_2121)=k9_relat_1('#skF_8', D_2121))), inference(resolution, [status(thm)], [c_26001, c_26445])).
% 15.73/7.40  tff(c_26000, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_25992, c_62])).
% 15.73/7.40  tff(c_26449, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_26448, c_26000])).
% 15.73/7.40  tff(c_26714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26707, c_26449])).
% 15.73/7.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.73/7.40  
% 15.73/7.40  Inference rules
% 15.73/7.40  ----------------------
% 15.73/7.40  #Ref     : 0
% 15.73/7.40  #Sup     : 6247
% 15.73/7.40  #Fact    : 0
% 15.73/7.40  #Define  : 0
% 15.73/7.40  #Split   : 23
% 15.73/7.40  #Chain   : 0
% 15.73/7.40  #Close   : 0
% 15.73/7.40  
% 15.73/7.40  Ordering : KBO
% 15.73/7.40  
% 15.73/7.40  Simplification rules
% 15.73/7.40  ----------------------
% 15.73/7.40  #Subsume      : 2550
% 15.73/7.40  #Demod        : 913
% 15.73/7.40  #Tautology    : 192
% 15.73/7.40  #SimpNegUnit  : 78
% 15.73/7.40  #BackRed      : 19
% 15.73/7.40  
% 15.73/7.40  #Partial instantiations: 0
% 15.73/7.40  #Strategies tried      : 1
% 15.73/7.40  
% 15.73/7.40  Timing (in seconds)
% 15.73/7.40  ----------------------
% 15.73/7.41  Preprocessing        : 0.36
% 15.73/7.41  Parsing              : 0.19
% 15.73/7.41  CNF conversion       : 0.03
% 15.73/7.41  Main loop            : 6.24
% 15.73/7.41  Inferencing          : 1.19
% 15.73/7.41  Reduction            : 1.20
% 15.73/7.41  Demodulation         : 0.80
% 15.73/7.41  BG Simplification    : 0.10
% 15.73/7.41  Subsumption          : 3.36
% 15.73/7.41  Abstraction          : 0.17
% 15.73/7.41  MUC search           : 0.00
% 15.73/7.41  Cooper               : 0.00
% 15.73/7.41  Total                : 6.65
% 15.73/7.41  Index Insertion      : 0.00
% 15.73/7.41  Index Deletion       : 0.00
% 15.73/7.41  Index Matching       : 0.00
% 15.73/7.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
