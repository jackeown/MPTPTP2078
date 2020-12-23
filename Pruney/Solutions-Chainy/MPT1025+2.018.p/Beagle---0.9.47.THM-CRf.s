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
% DateTime   : Thu Dec  3 10:16:32 EST 2020

% Result     : Theorem 13.62s
% Output     : CNFRefutation 13.91s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 813 expanded)
%              Number of leaves         :   41 ( 295 expanded)
%              Depth                    :   15
%              Number of atoms          :  344 (2278 expanded)
%              Number of equality atoms :   24 ( 262 expanded)
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

tff(f_141,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_122,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_72,plain,(
    ! [C_145,A_146,B_147] :
      ( v1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [A_200,B_201,C_202] :
      ( r2_hidden('#skF_3'(A_200,B_201,C_202),B_201)
      | ~ r2_hidden(A_200,k9_relat_1(C_202,B_201))
      | ~ v1_relat_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_259,plain,(
    ! [B_203,A_204,C_205] :
      ( ~ v1_xboole_0(B_203)
      | ~ r2_hidden(A_204,k9_relat_1(C_205,B_203))
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_246,c_2])).

tff(c_284,plain,(
    ! [B_203,C_205] :
      ( ~ v1_xboole_0(B_203)
      | ~ v1_relat_1(C_205)
      | v1_xboole_0(k9_relat_1(C_205,B_203)) ) ),
    inference(resolution,[status(thm)],[c_4,c_259])).

tff(c_518,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k7_relset_1(A_257,B_258,C_259,D_260) = k9_relat_1(C_259,D_260)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_525,plain,(
    ! [D_260] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_260) = k9_relat_1('#skF_8',D_260) ),
    inference(resolution,[status(thm)],[c_56,c_518])).

tff(c_54,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_70,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_527,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_70])).

tff(c_548,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_284,c_527])).

tff(c_554,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_548])).

tff(c_528,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_54])).

tff(c_529,plain,(
    ! [D_261] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_261) = k9_relat_1('#skF_8',D_261) ),
    inference(resolution,[status(thm)],[c_56,c_518])).

tff(c_40,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( m1_subset_1(k7_relset_1(A_33,B_34,C_35,D_36),k1_zfmisc_1(B_34))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_535,plain,(
    ! [D_261] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_261),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_40])).

tff(c_610,plain,(
    ! [D_265] : m1_subset_1(k9_relat_1('#skF_8',D_265),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_535])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_681,plain,(
    ! [A_269,D_270] :
      ( m1_subset_1(A_269,'#skF_6')
      | ~ r2_hidden(A_269,k9_relat_1('#skF_8',D_270)) ) ),
    inference(resolution,[status(thm)],[c_610,c_12])).

tff(c_709,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_528,c_681])).

tff(c_14,plain,(
    ! [C_15,B_14,A_13] :
      ( ~ v1_xboole_0(C_15)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(C_15))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_616,plain,(
    ! [A_13,D_265] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_8',D_265)) ) ),
    inference(resolution,[status(thm)],[c_610,c_14])).

tff(c_654,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_145,plain,(
    ! [C_168,A_169,B_170] :
      ( v4_relat_1(C_168,A_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_149,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [C_161,B_162,A_163] :
      ( r2_hidden(C_161,B_162)
      | ~ r2_hidden(C_161,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_155,plain,(
    ! [A_174,B_175] :
      ( r2_hidden('#skF_1'(A_174),B_175)
      | ~ r1_tarski(A_174,B_175)
      | v1_xboole_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_168,plain,(
    ! [B_176,A_177] :
      ( ~ v1_xboole_0(B_176)
      | ~ r1_tarski(A_177,B_176)
      | v1_xboole_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_187,plain,(
    ! [A_182,B_183] :
      ( ~ v1_xboole_0(A_182)
      | v1_xboole_0(k1_relat_1(B_183))
      | ~ v4_relat_1(B_183,A_182)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_18,c_168])).

tff(c_189,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_149,c_187])).

tff(c_194,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_189])).

tff(c_196,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_1288,plain,(
    ! [C_323,D_327,E_325,A_324,B_326] :
      ( r2_hidden('#skF_4'(C_323,A_324,E_325,B_326,D_327),B_326)
      | ~ r2_hidden(E_325,k7_relset_1(C_323,A_324,D_327,B_326))
      | ~ m1_subset_1(E_325,A_324)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(k2_zfmisc_1(C_323,A_324)))
      | v1_xboole_0(C_323)
      | v1_xboole_0(B_326)
      | v1_xboole_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1293,plain,(
    ! [E_325,B_326] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',E_325,B_326,'#skF_8'),B_326)
      | ~ r2_hidden(E_325,k7_relset_1('#skF_5','#skF_6','#skF_8',B_326))
      | ~ m1_subset_1(E_325,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_326)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_1288])).

tff(c_1296,plain,(
    ! [E_325,B_326] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',E_325,B_326,'#skF_8'),B_326)
      | ~ r2_hidden(E_325,k9_relat_1('#skF_8',B_326))
      | ~ m1_subset_1(E_325,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_326)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_1293])).

tff(c_4476,plain,(
    ! [E_644,B_645] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',E_644,B_645,'#skF_8'),B_645)
      | ~ r2_hidden(E_644,k9_relat_1('#skF_8',B_645))
      | ~ m1_subset_1(E_644,'#skF_6')
      | v1_xboole_0(B_645) ) ),
    inference(negUnitSimplification,[status(thm)],[c_654,c_196,c_1296])).

tff(c_52,plain,(
    ! [F_139] :
      ( k1_funct_1('#skF_8',F_139) != '#skF_9'
      | ~ r2_hidden(F_139,'#skF_7')
      | ~ m1_subset_1(F_139,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4564,plain,(
    ! [E_644] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',E_644,'#skF_7','#skF_8')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',E_644,'#skF_7','#skF_8'),'#skF_5')
      | ~ r2_hidden(E_644,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_644,'#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4476,c_52])).

tff(c_4618,plain,(
    ! [E_652] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',E_652,'#skF_7','#skF_8')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',E_652,'#skF_7','#skF_8'),'#skF_5')
      | ~ r2_hidden(E_652,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_652,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_4564])).

tff(c_4661,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_528,c_4618])).

tff(c_4700,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_4661])).

tff(c_10501,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4700])).

tff(c_83,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_2'(A_149,B_150),A_149)
      | r1_tarski(A_149,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_149] : r1_tarski(A_149,A_149) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_3'(A_18,B_19,C_20),k1_relat_1(C_20))
      | ~ r2_hidden(A_18,k9_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_555,plain,(
    ! [A_262,B_263,C_264] :
      ( r2_hidden(k4_tarski('#skF_3'(A_262,B_263,C_264),A_262),C_264)
      | ~ r2_hidden(A_262,k9_relat_1(C_264,B_263))
      | ~ v1_relat_1(C_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [C_26,A_24,B_25] :
      ( k1_funct_1(C_26,A_24) = B_25
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2802,plain,(
    ! [C_487,A_488,B_489] :
      ( k1_funct_1(C_487,'#skF_3'(A_488,B_489,C_487)) = A_488
      | ~ v1_funct_1(C_487)
      | ~ r2_hidden(A_488,k9_relat_1(C_487,B_489))
      | ~ v1_relat_1(C_487) ) ),
    inference(resolution,[status(thm)],[c_555,c_30])).

tff(c_2818,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_528,c_2802])).

tff(c_2844,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_60,c_2818])).

tff(c_28,plain,(
    ! [A_24,C_26] :
      ( r2_hidden(k4_tarski(A_24,k1_funct_1(C_26,A_24)),C_26)
      | ~ r2_hidden(A_24,k1_relat_1(C_26))
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2854,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_28])).

tff(c_2858,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_60,c_2854])).

tff(c_2860,plain,(
    ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2858])).

tff(c_2866,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_2860])).

tff(c_2873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_528,c_2866])).

tff(c_2874,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2858])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3194,plain,(
    ! [B_512] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_512)
      | ~ r1_tarski('#skF_8',B_512) ) ),
    inference(resolution,[status(thm)],[c_2874,c_6])).

tff(c_32,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(A_24,k1_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3305,plain,(
    ! [B_512] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_512))
      | ~ v1_funct_1(B_512)
      | ~ v1_relat_1(B_512)
      | ~ r1_tarski('#skF_8',B_512) ) ),
    inference(resolution,[status(thm)],[c_3194,c_32])).

tff(c_2983,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_6)
      | ~ r1_tarski('#skF_8',B_6) ) ),
    inference(resolution,[status(thm)],[c_2874,c_6])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_3'(A_18,B_19,C_20),B_19)
      | ~ r2_hidden(A_18,k9_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_899,plain,(
    ! [A_284,C_285,B_286,D_287] :
      ( r2_hidden(A_284,k9_relat_1(C_285,B_286))
      | ~ r2_hidden(D_287,B_286)
      | ~ r2_hidden(k4_tarski(D_287,A_284),C_285)
      | ~ r2_hidden(D_287,k1_relat_1(C_285))
      | ~ v1_relat_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5971,plain,(
    ! [B_807,A_808,C_806,A_804,C_805] :
      ( r2_hidden(A_808,k9_relat_1(C_806,B_807))
      | ~ r2_hidden(k4_tarski('#skF_3'(A_804,B_807,C_805),A_808),C_806)
      | ~ r2_hidden('#skF_3'(A_804,B_807,C_805),k1_relat_1(C_806))
      | ~ v1_relat_1(C_806)
      | ~ r2_hidden(A_804,k9_relat_1(C_805,B_807))
      | ~ v1_relat_1(C_805) ) ),
    inference(resolution,[status(thm)],[c_22,c_899])).

tff(c_5981,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_9',k9_relat_1(B_6,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',B_6) ) ),
    inference(resolution,[status(thm)],[c_2983,c_5971])).

tff(c_10762,plain,(
    ! [B_1201] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1201,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1201))
      | ~ v1_relat_1(B_1201)
      | ~ r1_tarski('#skF_8',B_1201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_528,c_5981])).

tff(c_10790,plain,(
    ! [B_512] :
      ( r2_hidden('#skF_9',k9_relat_1(B_512,'#skF_7'))
      | ~ v1_funct_1(B_512)
      | ~ v1_relat_1(B_512)
      | ~ r1_tarski('#skF_8',B_512) ) ),
    inference(resolution,[status(thm)],[c_3305,c_10762])).

tff(c_1125,plain,(
    ! [E_308,C_306,A_307,B_309,D_310] :
      ( m1_subset_1('#skF_4'(C_306,A_307,E_308,B_309,D_310),C_306)
      | ~ r2_hidden(E_308,k7_relset_1(C_306,A_307,D_310,B_309))
      | ~ m1_subset_1(E_308,A_307)
      | ~ m1_subset_1(D_310,k1_zfmisc_1(k2_zfmisc_1(C_306,A_307)))
      | v1_xboole_0(C_306)
      | v1_xboole_0(B_309)
      | v1_xboole_0(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1133,plain,(
    ! [E_308,D_260] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',E_308,D_260,'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_308,k9_relat_1('#skF_8',D_260))
      | ~ m1_subset_1(E_308,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_260)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_1125])).

tff(c_1152,plain,(
    ! [E_308,D_260] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',E_308,D_260,'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_308,k9_relat_1('#skF_8',D_260))
      | ~ m1_subset_1(E_308,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_260)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1133])).

tff(c_14969,plain,(
    ! [E_1466,D_1467] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',E_1466,D_1467,'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_1466,k9_relat_1('#skF_8',D_1467))
      | ~ m1_subset_1(E_1466,'#skF_6')
      | v1_xboole_0(D_1467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_654,c_196,c_1152])).

tff(c_14997,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_10790,c_14969])).

tff(c_15106,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76,c_60,c_709,c_14997])).

tff(c_15108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_10501,c_15106])).

tff(c_15109,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4700])).

tff(c_15419,plain,(
    ! [B_1515] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1515,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1515))
      | ~ v1_relat_1(B_1515)
      | ~ r1_tarski('#skF_8',B_1515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_528,c_5981])).

tff(c_15447,plain,(
    ! [B_512] :
      ( r2_hidden('#skF_9',k9_relat_1(B_512,'#skF_7'))
      | ~ v1_funct_1(B_512)
      | ~ v1_relat_1(B_512)
      | ~ r1_tarski('#skF_8',B_512) ) ),
    inference(resolution,[status(thm)],[c_3305,c_15419])).

tff(c_1555,plain,(
    ! [C_356,A_357,E_358,B_359,D_360] :
      ( r2_hidden(k4_tarski('#skF_4'(C_356,A_357,E_358,B_359,D_360),E_358),D_360)
      | ~ r2_hidden(E_358,k7_relset_1(C_356,A_357,D_360,B_359))
      | ~ m1_subset_1(E_358,A_357)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(C_356,A_357)))
      | v1_xboole_0(C_356)
      | v1_xboole_0(B_359)
      | v1_xboole_0(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_7574,plain,(
    ! [A_949,C_950,D_948,B_951,E_947] :
      ( k1_funct_1(D_948,'#skF_4'(C_950,A_949,E_947,B_951,D_948)) = E_947
      | ~ v1_funct_1(D_948)
      | ~ v1_relat_1(D_948)
      | ~ r2_hidden(E_947,k7_relset_1(C_950,A_949,D_948,B_951))
      | ~ m1_subset_1(E_947,A_949)
      | ~ m1_subset_1(D_948,k1_zfmisc_1(k2_zfmisc_1(C_950,A_949)))
      | v1_xboole_0(C_950)
      | v1_xboole_0(B_951)
      | v1_xboole_0(A_949) ) ),
    inference(resolution,[status(thm)],[c_1555,c_30])).

tff(c_7618,plain,(
    ! [E_947,D_260] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',E_947,D_260,'#skF_8')) = E_947
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(E_947,k9_relat_1('#skF_8',D_260))
      | ~ m1_subset_1(E_947,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_260)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_7574])).

tff(c_7649,plain,(
    ! [E_947,D_260] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',E_947,D_260,'#skF_8')) = E_947
      | ~ r2_hidden(E_947,k9_relat_1('#skF_8',D_260))
      | ~ m1_subset_1(E_947,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_260)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76,c_60,c_7618])).

tff(c_23235,plain,(
    ! [E_1951,D_1952] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',E_1951,D_1952,'#skF_8')) = E_1951
      | ~ r2_hidden(E_1951,k9_relat_1('#skF_8',D_1952))
      | ~ m1_subset_1(E_1951,'#skF_6')
      | v1_xboole_0(D_1952) ) ),
    inference(negUnitSimplification,[status(thm)],[c_654,c_196,c_7649])).

tff(c_23271,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_15447,c_23235])).

tff(c_23387,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76,c_60,c_709,c_23271])).

tff(c_23389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_15109,c_23387])).

tff(c_23390,plain,(
    ! [A_13,D_265] : ~ r2_hidden(A_13,k9_relat_1('#skF_8',D_265)) ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_23393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23390,c_528])).

tff(c_23394,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_23690,plain,(
    ! [A_1998,B_1999,C_2000,D_2001] :
      ( k7_relset_1(A_1998,B_1999,C_2000,D_2001) = k9_relat_1(C_2000,D_2001)
      | ~ m1_subset_1(C_2000,k1_zfmisc_1(k2_zfmisc_1(A_1998,B_1999))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_23693,plain,(
    ! [D_2001] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_2001) = k9_relat_1('#skF_8',D_2001) ),
    inference(resolution,[status(thm)],[c_56,c_23690])).

tff(c_23696,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23693,c_54])).

tff(c_23899,plain,(
    ! [A_2027,B_2028,C_2029] :
      ( r2_hidden('#skF_3'(A_2027,B_2028,C_2029),k1_relat_1(C_2029))
      | ~ r2_hidden(A_2027,k9_relat_1(C_2029,B_2028))
      | ~ v1_relat_1(C_2029) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_23907,plain,(
    ! [C_2030,A_2031,B_2032] :
      ( ~ v1_xboole_0(k1_relat_1(C_2030))
      | ~ r2_hidden(A_2031,k9_relat_1(C_2030,B_2032))
      | ~ v1_relat_1(C_2030) ) ),
    inference(resolution,[status(thm)],[c_23899,c_2])).

tff(c_23910,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_23696,c_23907])).

tff(c_23934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_23394,c_23910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.62/6.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.62/6.39  
% 13.62/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.62/6.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 13.62/6.39  
% 13.62/6.39  %Foreground sorts:
% 13.62/6.39  
% 13.62/6.39  
% 13.62/6.39  %Background operators:
% 13.62/6.39  
% 13.62/6.39  
% 13.62/6.39  %Foreground operators:
% 13.62/6.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.62/6.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.62/6.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.62/6.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.62/6.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.62/6.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 13.62/6.39  tff('#skF_7', type, '#skF_7': $i).
% 13.62/6.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.62/6.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.62/6.39  tff('#skF_5', type, '#skF_5': $i).
% 13.62/6.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.62/6.39  tff('#skF_6', type, '#skF_6': $i).
% 13.62/6.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.62/6.39  tff('#skF_9', type, '#skF_9': $i).
% 13.62/6.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.62/6.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.62/6.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.62/6.39  tff('#skF_8', type, '#skF_8': $i).
% 13.62/6.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.62/6.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.62/6.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.62/6.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.62/6.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.62/6.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.62/6.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.62/6.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.62/6.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.62/6.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.62/6.39  
% 13.91/6.42  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 13.91/6.42  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.91/6.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.91/6.42  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 13.91/6.42  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.91/6.42  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 13.91/6.42  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 13.91/6.42  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 13.91/6.42  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.91/6.42  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.91/6.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.91/6.42  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 13.91/6.42  tff(f_78, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 13.91/6.42  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.91/6.42  tff(c_72, plain, (![C_145, A_146, B_147]: (v1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.91/6.42  tff(c_76, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_72])).
% 13.91/6.42  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.91/6.42  tff(c_246, plain, (![A_200, B_201, C_202]: (r2_hidden('#skF_3'(A_200, B_201, C_202), B_201) | ~r2_hidden(A_200, k9_relat_1(C_202, B_201)) | ~v1_relat_1(C_202))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.91/6.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.91/6.42  tff(c_259, plain, (![B_203, A_204, C_205]: (~v1_xboole_0(B_203) | ~r2_hidden(A_204, k9_relat_1(C_205, B_203)) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_246, c_2])).
% 13.91/6.42  tff(c_284, plain, (![B_203, C_205]: (~v1_xboole_0(B_203) | ~v1_relat_1(C_205) | v1_xboole_0(k9_relat_1(C_205, B_203)))), inference(resolution, [status(thm)], [c_4, c_259])).
% 13.91/6.42  tff(c_518, plain, (![A_257, B_258, C_259, D_260]: (k7_relset_1(A_257, B_258, C_259, D_260)=k9_relat_1(C_259, D_260) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.91/6.42  tff(c_525, plain, (![D_260]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_260)=k9_relat_1('#skF_8', D_260))), inference(resolution, [status(thm)], [c_56, c_518])).
% 13.91/6.42  tff(c_54, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.91/6.42  tff(c_70, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 13.91/6.42  tff(c_527, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_70])).
% 13.91/6.42  tff(c_548, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_284, c_527])).
% 13.91/6.42  tff(c_554, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_548])).
% 13.91/6.42  tff(c_528, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_54])).
% 13.91/6.42  tff(c_529, plain, (![D_261]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_261)=k9_relat_1('#skF_8', D_261))), inference(resolution, [status(thm)], [c_56, c_518])).
% 13.91/6.42  tff(c_40, plain, (![A_33, B_34, C_35, D_36]: (m1_subset_1(k7_relset_1(A_33, B_34, C_35, D_36), k1_zfmisc_1(B_34)) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.91/6.42  tff(c_535, plain, (![D_261]: (m1_subset_1(k9_relat_1('#skF_8', D_261), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_529, c_40])).
% 13.91/6.42  tff(c_610, plain, (![D_265]: (m1_subset_1(k9_relat_1('#skF_8', D_265), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_535])).
% 13.91/6.42  tff(c_12, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.91/6.42  tff(c_681, plain, (![A_269, D_270]: (m1_subset_1(A_269, '#skF_6') | ~r2_hidden(A_269, k9_relat_1('#skF_8', D_270)))), inference(resolution, [status(thm)], [c_610, c_12])).
% 13.91/6.42  tff(c_709, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_528, c_681])).
% 13.91/6.42  tff(c_14, plain, (![C_15, B_14, A_13]: (~v1_xboole_0(C_15) | ~m1_subset_1(B_14, k1_zfmisc_1(C_15)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.91/6.42  tff(c_616, plain, (![A_13, D_265]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_13, k9_relat_1('#skF_8', D_265)))), inference(resolution, [status(thm)], [c_610, c_14])).
% 13.91/6.42  tff(c_654, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_616])).
% 13.91/6.42  tff(c_145, plain, (![C_168, A_169, B_170]: (v4_relat_1(C_168, A_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.91/6.42  tff(c_149, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_145])).
% 13.91/6.42  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.91/6.42  tff(c_118, plain, (![C_161, B_162, A_163]: (r2_hidden(C_161, B_162) | ~r2_hidden(C_161, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.91/6.42  tff(c_155, plain, (![A_174, B_175]: (r2_hidden('#skF_1'(A_174), B_175) | ~r1_tarski(A_174, B_175) | v1_xboole_0(A_174))), inference(resolution, [status(thm)], [c_4, c_118])).
% 13.91/6.42  tff(c_168, plain, (![B_176, A_177]: (~v1_xboole_0(B_176) | ~r1_tarski(A_177, B_176) | v1_xboole_0(A_177))), inference(resolution, [status(thm)], [c_155, c_2])).
% 13.91/6.42  tff(c_187, plain, (![A_182, B_183]: (~v1_xboole_0(A_182) | v1_xboole_0(k1_relat_1(B_183)) | ~v4_relat_1(B_183, A_182) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_18, c_168])).
% 13.91/6.42  tff(c_189, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_149, c_187])).
% 13.91/6.42  tff(c_194, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_189])).
% 13.91/6.42  tff(c_196, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_194])).
% 13.91/6.42  tff(c_1288, plain, (![C_323, D_327, E_325, A_324, B_326]: (r2_hidden('#skF_4'(C_323, A_324, E_325, B_326, D_327), B_326) | ~r2_hidden(E_325, k7_relset_1(C_323, A_324, D_327, B_326)) | ~m1_subset_1(E_325, A_324) | ~m1_subset_1(D_327, k1_zfmisc_1(k2_zfmisc_1(C_323, A_324))) | v1_xboole_0(C_323) | v1_xboole_0(B_326) | v1_xboole_0(A_324))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.91/6.42  tff(c_1293, plain, (![E_325, B_326]: (r2_hidden('#skF_4'('#skF_5', '#skF_6', E_325, B_326, '#skF_8'), B_326) | ~r2_hidden(E_325, k7_relset_1('#skF_5', '#skF_6', '#skF_8', B_326)) | ~m1_subset_1(E_325, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_326) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_1288])).
% 13.91/6.42  tff(c_1296, plain, (![E_325, B_326]: (r2_hidden('#skF_4'('#skF_5', '#skF_6', E_325, B_326, '#skF_8'), B_326) | ~r2_hidden(E_325, k9_relat_1('#skF_8', B_326)) | ~m1_subset_1(E_325, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_326) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_1293])).
% 13.91/6.42  tff(c_4476, plain, (![E_644, B_645]: (r2_hidden('#skF_4'('#skF_5', '#skF_6', E_644, B_645, '#skF_8'), B_645) | ~r2_hidden(E_644, k9_relat_1('#skF_8', B_645)) | ~m1_subset_1(E_644, '#skF_6') | v1_xboole_0(B_645))), inference(negUnitSimplification, [status(thm)], [c_654, c_196, c_1296])).
% 13.91/6.42  tff(c_52, plain, (![F_139]: (k1_funct_1('#skF_8', F_139)!='#skF_9' | ~r2_hidden(F_139, '#skF_7') | ~m1_subset_1(F_139, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.91/6.42  tff(c_4564, plain, (![E_644]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', E_644, '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', E_644, '#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden(E_644, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_644, '#skF_6') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_4476, c_52])).
% 13.91/6.42  tff(c_4618, plain, (![E_652]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', E_652, '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', E_652, '#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden(E_652, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_652, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_554, c_4564])).
% 13.91/6.42  tff(c_4661, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_528, c_4618])).
% 13.91/6.42  tff(c_4700, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_709, c_4661])).
% 13.91/6.42  tff(c_10501, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4700])).
% 13.91/6.42  tff(c_83, plain, (![A_149, B_150]: (r2_hidden('#skF_2'(A_149, B_150), A_149) | r1_tarski(A_149, B_150))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.91/6.42  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.91/6.42  tff(c_96, plain, (![A_149]: (r1_tarski(A_149, A_149))), inference(resolution, [status(thm)], [c_83, c_8])).
% 13.91/6.42  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.91/6.42  tff(c_26, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_3'(A_18, B_19, C_20), k1_relat_1(C_20)) | ~r2_hidden(A_18, k9_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.91/6.42  tff(c_555, plain, (![A_262, B_263, C_264]: (r2_hidden(k4_tarski('#skF_3'(A_262, B_263, C_264), A_262), C_264) | ~r2_hidden(A_262, k9_relat_1(C_264, B_263)) | ~v1_relat_1(C_264))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.91/6.42  tff(c_30, plain, (![C_26, A_24, B_25]: (k1_funct_1(C_26, A_24)=B_25 | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.91/6.42  tff(c_2802, plain, (![C_487, A_488, B_489]: (k1_funct_1(C_487, '#skF_3'(A_488, B_489, C_487))=A_488 | ~v1_funct_1(C_487) | ~r2_hidden(A_488, k9_relat_1(C_487, B_489)) | ~v1_relat_1(C_487))), inference(resolution, [status(thm)], [c_555, c_30])).
% 13.91/6.42  tff(c_2818, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_528, c_2802])).
% 13.91/6.42  tff(c_2844, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_60, c_2818])).
% 13.91/6.42  tff(c_28, plain, (![A_24, C_26]: (r2_hidden(k4_tarski(A_24, k1_funct_1(C_26, A_24)), C_26) | ~r2_hidden(A_24, k1_relat_1(C_26)) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.91/6.42  tff(c_2854, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2844, c_28])).
% 13.91/6.42  tff(c_2858, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_60, c_2854])).
% 13.91/6.42  tff(c_2860, plain, (~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_2858])).
% 13.91/6.42  tff(c_2866, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_2860])).
% 13.91/6.42  tff(c_2873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_528, c_2866])).
% 13.91/6.42  tff(c_2874, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_2858])).
% 13.91/6.42  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.91/6.42  tff(c_3194, plain, (![B_512]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_512) | ~r1_tarski('#skF_8', B_512))), inference(resolution, [status(thm)], [c_2874, c_6])).
% 13.91/6.42  tff(c_32, plain, (![A_24, C_26, B_25]: (r2_hidden(A_24, k1_relat_1(C_26)) | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.91/6.42  tff(c_3305, plain, (![B_512]: (r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_512)) | ~v1_funct_1(B_512) | ~v1_relat_1(B_512) | ~r1_tarski('#skF_8', B_512))), inference(resolution, [status(thm)], [c_3194, c_32])).
% 13.91/6.42  tff(c_2983, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_6) | ~r1_tarski('#skF_8', B_6))), inference(resolution, [status(thm)], [c_2874, c_6])).
% 13.91/6.42  tff(c_22, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_3'(A_18, B_19, C_20), B_19) | ~r2_hidden(A_18, k9_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.91/6.42  tff(c_899, plain, (![A_284, C_285, B_286, D_287]: (r2_hidden(A_284, k9_relat_1(C_285, B_286)) | ~r2_hidden(D_287, B_286) | ~r2_hidden(k4_tarski(D_287, A_284), C_285) | ~r2_hidden(D_287, k1_relat_1(C_285)) | ~v1_relat_1(C_285))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.91/6.42  tff(c_5971, plain, (![B_807, A_808, C_806, A_804, C_805]: (r2_hidden(A_808, k9_relat_1(C_806, B_807)) | ~r2_hidden(k4_tarski('#skF_3'(A_804, B_807, C_805), A_808), C_806) | ~r2_hidden('#skF_3'(A_804, B_807, C_805), k1_relat_1(C_806)) | ~v1_relat_1(C_806) | ~r2_hidden(A_804, k9_relat_1(C_805, B_807)) | ~v1_relat_1(C_805))), inference(resolution, [status(thm)], [c_22, c_899])).
% 13.91/6.42  tff(c_5981, plain, (![B_6]: (r2_hidden('#skF_9', k9_relat_1(B_6, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_6)) | ~v1_relat_1(B_6) | ~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', B_6))), inference(resolution, [status(thm)], [c_2983, c_5971])).
% 13.91/6.42  tff(c_10762, plain, (![B_1201]: (r2_hidden('#skF_9', k9_relat_1(B_1201, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1201)) | ~v1_relat_1(B_1201) | ~r1_tarski('#skF_8', B_1201))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_528, c_5981])).
% 13.91/6.42  tff(c_10790, plain, (![B_512]: (r2_hidden('#skF_9', k9_relat_1(B_512, '#skF_7')) | ~v1_funct_1(B_512) | ~v1_relat_1(B_512) | ~r1_tarski('#skF_8', B_512))), inference(resolution, [status(thm)], [c_3305, c_10762])).
% 13.91/6.42  tff(c_1125, plain, (![E_308, C_306, A_307, B_309, D_310]: (m1_subset_1('#skF_4'(C_306, A_307, E_308, B_309, D_310), C_306) | ~r2_hidden(E_308, k7_relset_1(C_306, A_307, D_310, B_309)) | ~m1_subset_1(E_308, A_307) | ~m1_subset_1(D_310, k1_zfmisc_1(k2_zfmisc_1(C_306, A_307))) | v1_xboole_0(C_306) | v1_xboole_0(B_309) | v1_xboole_0(A_307))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.91/6.42  tff(c_1133, plain, (![E_308, D_260]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', E_308, D_260, '#skF_8'), '#skF_5') | ~r2_hidden(E_308, k9_relat_1('#skF_8', D_260)) | ~m1_subset_1(E_308, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_260) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_525, c_1125])).
% 13.91/6.42  tff(c_1152, plain, (![E_308, D_260]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', E_308, D_260, '#skF_8'), '#skF_5') | ~r2_hidden(E_308, k9_relat_1('#skF_8', D_260)) | ~m1_subset_1(E_308, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_260) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1133])).
% 13.91/6.42  tff(c_14969, plain, (![E_1466, D_1467]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', E_1466, D_1467, '#skF_8'), '#skF_5') | ~r2_hidden(E_1466, k9_relat_1('#skF_8', D_1467)) | ~m1_subset_1(E_1466, '#skF_6') | v1_xboole_0(D_1467))), inference(negUnitSimplification, [status(thm)], [c_654, c_196, c_1152])).
% 13.91/6.42  tff(c_14997, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_10790, c_14969])).
% 13.91/6.42  tff(c_15106, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'), '#skF_5') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76, c_60, c_709, c_14997])).
% 13.91/6.42  tff(c_15108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_554, c_10501, c_15106])).
% 13.91/6.42  tff(c_15109, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(splitRight, [status(thm)], [c_4700])).
% 13.91/6.42  tff(c_15419, plain, (![B_1515]: (r2_hidden('#skF_9', k9_relat_1(B_1515, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1515)) | ~v1_relat_1(B_1515) | ~r1_tarski('#skF_8', B_1515))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_528, c_5981])).
% 13.91/6.42  tff(c_15447, plain, (![B_512]: (r2_hidden('#skF_9', k9_relat_1(B_512, '#skF_7')) | ~v1_funct_1(B_512) | ~v1_relat_1(B_512) | ~r1_tarski('#skF_8', B_512))), inference(resolution, [status(thm)], [c_3305, c_15419])).
% 13.91/6.42  tff(c_1555, plain, (![C_356, A_357, E_358, B_359, D_360]: (r2_hidden(k4_tarski('#skF_4'(C_356, A_357, E_358, B_359, D_360), E_358), D_360) | ~r2_hidden(E_358, k7_relset_1(C_356, A_357, D_360, B_359)) | ~m1_subset_1(E_358, A_357) | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(C_356, A_357))) | v1_xboole_0(C_356) | v1_xboole_0(B_359) | v1_xboole_0(A_357))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.91/6.42  tff(c_7574, plain, (![A_949, C_950, D_948, B_951, E_947]: (k1_funct_1(D_948, '#skF_4'(C_950, A_949, E_947, B_951, D_948))=E_947 | ~v1_funct_1(D_948) | ~v1_relat_1(D_948) | ~r2_hidden(E_947, k7_relset_1(C_950, A_949, D_948, B_951)) | ~m1_subset_1(E_947, A_949) | ~m1_subset_1(D_948, k1_zfmisc_1(k2_zfmisc_1(C_950, A_949))) | v1_xboole_0(C_950) | v1_xboole_0(B_951) | v1_xboole_0(A_949))), inference(resolution, [status(thm)], [c_1555, c_30])).
% 13.91/6.42  tff(c_7618, plain, (![E_947, D_260]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', E_947, D_260, '#skF_8'))=E_947 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(E_947, k9_relat_1('#skF_8', D_260)) | ~m1_subset_1(E_947, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_260) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_525, c_7574])).
% 13.91/6.42  tff(c_7649, plain, (![E_947, D_260]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', E_947, D_260, '#skF_8'))=E_947 | ~r2_hidden(E_947, k9_relat_1('#skF_8', D_260)) | ~m1_subset_1(E_947, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_260) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76, c_60, c_7618])).
% 13.91/6.42  tff(c_23235, plain, (![E_1951, D_1952]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', E_1951, D_1952, '#skF_8'))=E_1951 | ~r2_hidden(E_1951, k9_relat_1('#skF_8', D_1952)) | ~m1_subset_1(E_1951, '#skF_6') | v1_xboole_0(D_1952))), inference(negUnitSimplification, [status(thm)], [c_654, c_196, c_7649])).
% 13.91/6.42  tff(c_23271, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_15447, c_23235])).
% 13.91/6.42  tff(c_23387, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_9', '#skF_7', '#skF_8'))='#skF_9' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76, c_60, c_709, c_23271])).
% 13.91/6.42  tff(c_23389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_554, c_15109, c_23387])).
% 13.91/6.42  tff(c_23390, plain, (![A_13, D_265]: (~r2_hidden(A_13, k9_relat_1('#skF_8', D_265)))), inference(splitRight, [status(thm)], [c_616])).
% 13.91/6.42  tff(c_23393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23390, c_528])).
% 13.91/6.42  tff(c_23394, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_194])).
% 13.91/6.42  tff(c_23690, plain, (![A_1998, B_1999, C_2000, D_2001]: (k7_relset_1(A_1998, B_1999, C_2000, D_2001)=k9_relat_1(C_2000, D_2001) | ~m1_subset_1(C_2000, k1_zfmisc_1(k2_zfmisc_1(A_1998, B_1999))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.91/6.42  tff(c_23693, plain, (![D_2001]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_2001)=k9_relat_1('#skF_8', D_2001))), inference(resolution, [status(thm)], [c_56, c_23690])).
% 13.91/6.42  tff(c_23696, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_23693, c_54])).
% 13.91/6.42  tff(c_23899, plain, (![A_2027, B_2028, C_2029]: (r2_hidden('#skF_3'(A_2027, B_2028, C_2029), k1_relat_1(C_2029)) | ~r2_hidden(A_2027, k9_relat_1(C_2029, B_2028)) | ~v1_relat_1(C_2029))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.91/6.42  tff(c_23907, plain, (![C_2030, A_2031, B_2032]: (~v1_xboole_0(k1_relat_1(C_2030)) | ~r2_hidden(A_2031, k9_relat_1(C_2030, B_2032)) | ~v1_relat_1(C_2030))), inference(resolution, [status(thm)], [c_23899, c_2])).
% 13.91/6.42  tff(c_23910, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_23696, c_23907])).
% 13.91/6.42  tff(c_23934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_23394, c_23910])).
% 13.91/6.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.91/6.42  
% 13.91/6.42  Inference rules
% 13.91/6.42  ----------------------
% 13.91/6.42  #Ref     : 0
% 13.91/6.42  #Sup     : 5448
% 13.91/6.42  #Fact    : 0
% 13.91/6.42  #Define  : 0
% 13.91/6.42  #Split   : 25
% 13.91/6.42  #Chain   : 0
% 13.91/6.42  #Close   : 0
% 13.91/6.42  
% 13.91/6.42  Ordering : KBO
% 13.91/6.42  
% 13.91/6.42  Simplification rules
% 13.91/6.42  ----------------------
% 13.91/6.42  #Subsume      : 2574
% 13.91/6.42  #Demod        : 843
% 13.91/6.42  #Tautology    : 132
% 13.91/6.42  #SimpNegUnit  : 88
% 13.91/6.42  #BackRed      : 19
% 13.91/6.42  
% 13.91/6.42  #Partial instantiations: 0
% 13.91/6.42  #Strategies tried      : 1
% 13.91/6.42  
% 13.91/6.42  Timing (in seconds)
% 13.91/6.42  ----------------------
% 13.91/6.42  Preprocessing        : 0.35
% 13.91/6.42  Parsing              : 0.18
% 13.91/6.42  CNF conversion       : 0.03
% 13.91/6.42  Main loop            : 5.27
% 13.91/6.42  Inferencing          : 1.09
% 13.91/6.42  Reduction            : 1.05
% 13.91/6.42  Demodulation         : 0.71
% 13.91/6.42  BG Simplification    : 0.08
% 13.91/6.42  Subsumption          : 2.74
% 13.91/6.42  Abstraction          : 0.13
% 13.91/6.42  MUC search           : 0.00
% 13.91/6.42  Cooper               : 0.00
% 13.91/6.42  Total                : 5.67
% 13.91/6.43  Index Insertion      : 0.00
% 13.91/6.43  Index Deletion       : 0.00
% 13.91/6.43  Index Matching       : 0.00
% 13.91/6.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
