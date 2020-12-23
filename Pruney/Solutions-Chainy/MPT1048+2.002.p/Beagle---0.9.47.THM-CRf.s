%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:08 EST 2020

% Result     : Theorem 16.69s
% Output     : CNFRefutation 16.69s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 420 expanded)
%              Number of leaves         :   29 ( 161 expanded)
%              Depth                    :   20
%              Number of atoms          :  264 (1513 expanded)
%              Number of equality atoms :    7 (  76 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_relset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_relset_1,type,(
    r1_relset_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_relset_1(A,B,D,C)
             => r1_tarski(k5_partfun1(A,B,C),k5_partfun1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_relat_1(E)
                & v1_funct_1(E) )
             => ( ( r1_partfun1(C,E)
                  & r1_relset_1(A,B,D,C) )
               => r1_partfun1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_partfun1)).

tff(c_50,plain,(
    ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_63,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [A_67] : r1_tarski(A_67,A_67) ),
    inference(resolution,[status(thm)],[c_63,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,(
    ! [C_72,B_73,A_74] :
      ( r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_1,B_2,B_73] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_73)
      | ~ r1_tarski(A_1,B_73)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_113,plain,(
    ! [C_88,A_89,B_90,E_91] :
      ( '#skF_5'(C_88,A_89,B_90,E_91,k5_partfun1(A_89,B_90,C_88)) = E_91
      | ~ r2_hidden(E_91,k5_partfun1(A_89,B_90,C_88))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_570,plain,(
    ! [C_215,A_218,A_216,B_214,B_217] :
      ( '#skF_5'(C_215,A_216,B_214,'#skF_1'(A_218,B_217),k5_partfun1(A_216,B_214,C_215)) = '#skF_1'(A_218,B_217)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_1(C_215)
      | ~ r1_tarski(A_218,k5_partfun1(A_216,B_214,C_215))
      | r1_tarski(A_218,B_217) ) ),
    inference(resolution,[status(thm)],[c_86,c_113])).

tff(c_576,plain,(
    ! [A_218,B_217] :
      ( '#skF_5'('#skF_8','#skF_6','#skF_7','#skF_1'(A_218,B_217),k5_partfun1('#skF_6','#skF_7','#skF_8')) = '#skF_1'(A_218,B_217)
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_218,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_218,B_217) ) ),
    inference(resolution,[status(thm)],[c_58,c_570])).

tff(c_587,plain,(
    ! [A_219,B_220] :
      ( '#skF_5'('#skF_8','#skF_6','#skF_7','#skF_1'(A_219,B_220),k5_partfun1('#skF_6','#skF_7','#skF_8')) = '#skF_1'(A_219,B_220)
      | ~ r1_tarski(A_219,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_219,B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_576])).

tff(c_96,plain,(
    ! [C_78,A_79,B_80,E_81] :
      ( v1_funct_1('#skF_5'(C_78,A_79,B_80,E_81,k5_partfun1(A_79,B_80,C_78)))
      | ~ r2_hidden(E_81,k5_partfun1(A_79,B_80,C_78))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [E_81] :
      ( v1_funct_1('#skF_5'('#skF_8','#skF_6','#skF_7',E_81,k5_partfun1('#skF_6','#skF_7','#skF_8')))
      | ~ r2_hidden(E_81,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_96])).

tff(c_103,plain,(
    ! [E_81] :
      ( v1_funct_1('#skF_5'('#skF_8','#skF_6','#skF_7',E_81,k5_partfun1('#skF_6','#skF_7','#skF_8')))
      | ~ r2_hidden(E_81,k5_partfun1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_98])).

tff(c_673,plain,(
    ! [A_232,B_233] :
      ( v1_funct_1('#skF_1'(A_232,B_233))
      | ~ r2_hidden('#skF_1'(A_232,B_233),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_232,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_232,B_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_103])).

tff(c_681,plain,(
    ! [B_2] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2))
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_673])).

tff(c_685,plain,(
    ! [B_2] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_681])).

tff(c_1059,plain,(
    ! [C_303,A_304,B_305,B_306] :
      ( '#skF_5'(C_303,A_304,B_305,'#skF_1'(k5_partfun1(A_304,B_305,C_303),B_306),k5_partfun1(A_304,B_305,C_303)) = '#skF_1'(k5_partfun1(A_304,B_305,C_303),B_306)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305)))
      | ~ v1_funct_1(C_303)
      | r1_tarski(k5_partfun1(A_304,B_305,C_303),B_306) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12,E_49] :
      ( r1_partfun1(C_13,'#skF_5'(C_13,A_11,B_12,E_49,k5_partfun1(A_11,B_12,C_13)))
      | ~ r2_hidden(E_49,k5_partfun1(A_11,B_12,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2867,plain,(
    ! [C_418,A_419,B_420,B_421] :
      ( r1_partfun1(C_418,'#skF_1'(k5_partfun1(A_419,B_420,C_418),B_421))
      | ~ r2_hidden('#skF_1'(k5_partfun1(A_419,B_420,C_418),B_421),k5_partfun1(A_419,B_420,C_418))
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420)))
      | ~ v1_funct_1(C_418)
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420)))
      | ~ v1_funct_1(C_418)
      | r1_tarski(k5_partfun1(A_419,B_420,C_418),B_421) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_14])).

tff(c_2871,plain,(
    ! [C_418,A_419,B_420,B_2] :
      ( r1_partfun1(C_418,'#skF_1'(k5_partfun1(A_419,B_420,C_418),B_2))
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420)))
      | ~ v1_funct_1(C_418)
      | ~ r1_tarski(k5_partfun1(A_419,B_420,C_418),k5_partfun1(A_419,B_420,C_418))
      | r1_tarski(k5_partfun1(A_419,B_420,C_418),B_2) ) ),
    inference(resolution,[status(thm)],[c_86,c_2867])).

tff(c_2878,plain,(
    ! [C_418,A_419,B_420,B_2] :
      ( r1_partfun1(C_418,'#skF_1'(k5_partfun1(A_419,B_420,C_418),B_2))
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420)))
      | ~ v1_funct_1(C_418)
      | r1_tarski(k5_partfun1(A_419,B_420,C_418),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2871])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_319,plain,(
    ! [C_159,A_160,B_161,E_162] :
      ( m1_subset_1('#skF_5'(C_159,A_160,B_161,E_162,k5_partfun1(A_160,B_161,C_159)),k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ r2_hidden(E_162,k5_partfun1(A_160,B_161,C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_332,plain,(
    ! [C_159,A_160,B_161,E_162] :
      ( v1_relat_1('#skF_5'(C_159,A_160,B_161,E_162,k5_partfun1(A_160,B_161,C_159)))
      | ~ v1_relat_1(k2_zfmisc_1(A_160,B_161))
      | ~ r2_hidden(E_162,k5_partfun1(A_160,B_161,C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(C_159) ) ),
    inference(resolution,[status(thm)],[c_319,c_8])).

tff(c_344,plain,(
    ! [C_163,A_164,B_165,E_166] :
      ( v1_relat_1('#skF_5'(C_163,A_164,B_165,E_166,k5_partfun1(A_164,B_165,C_163)))
      | ~ r2_hidden(E_166,k5_partfun1(A_164,B_165,C_163))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_1(C_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_332])).

tff(c_348,plain,(
    ! [E_166] :
      ( v1_relat_1('#skF_5'('#skF_8','#skF_6','#skF_7',E_166,k5_partfun1('#skF_6','#skF_7','#skF_8')))
      | ~ r2_hidden(E_166,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_344])).

tff(c_354,plain,(
    ! [E_166] :
      ( v1_relat_1('#skF_5'('#skF_8','#skF_6','#skF_7',E_166,k5_partfun1('#skF_6','#skF_7','#skF_8')))
      | ~ r2_hidden(E_166,k5_partfun1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_348])).

tff(c_617,plain,(
    ! [A_221,B_222] :
      ( v1_relat_1('#skF_1'(A_221,B_222))
      | ~ r2_hidden('#skF_1'(A_221,B_222),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_221,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_221,B_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_354])).

tff(c_625,plain,(
    ! [B_2] :
      ( v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2))
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_617])).

tff(c_629,plain,(
    ! [B_2] :
      ( v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_625])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12,E_49] :
      ( v1_partfun1('#skF_5'(C_13,A_11,B_12,E_49,k5_partfun1(A_11,B_12,C_13)),A_11)
      | ~ r2_hidden(E_49,k5_partfun1(A_11,B_12,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_602,plain,(
    ! [A_219,B_220] :
      ( v1_partfun1('#skF_1'(A_219,B_220),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_219,B_220),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_219,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_219,B_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_16])).

tff(c_737,plain,(
    ! [A_251,B_252] :
      ( v1_partfun1('#skF_1'(A_251,B_252),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_251,B_252),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_251,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_251,B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_602])).

tff(c_745,plain,(
    ! [B_2] :
      ( v1_partfun1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2),'#skF_6')
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_737])).

tff(c_749,plain,(
    ! [B_2] :
      ( v1_partfun1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2),'#skF_6')
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_745])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,(
    r1_relset_1('#skF_6','#skF_7','#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_503,plain,(
    ! [C_193,D_196,A_194,E_195,B_197] :
      ( r1_partfun1(D_196,E_195)
      | ~ r1_relset_1(A_194,B_197,D_196,C_193)
      | ~ r1_partfun1(C_193,E_195)
      | ~ v1_funct_1(E_195)
      | ~ v1_relat_1(E_195)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_197)))
      | ~ v1_funct_1(D_196)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_194,B_197)))
      | ~ v1_funct_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_505,plain,(
    ! [E_195] :
      ( r1_partfun1('#skF_9',E_195)
      | ~ r1_partfun1('#skF_8',E_195)
      | ~ v1_funct_1(E_195)
      | ~ v1_relat_1(E_195)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_503])).

tff(c_508,plain,(
    ! [E_195] :
      ( r1_partfun1('#skF_9',E_195)
      | ~ r1_partfun1('#skF_8',E_195)
      | ~ v1_funct_1(E_195)
      | ~ v1_relat_1(E_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_505])).

tff(c_20,plain,(
    ! [C_13,A_11,B_12,E_49] :
      ( m1_subset_1('#skF_5'(C_13,A_11,B_12,E_49,k5_partfun1(A_11,B_12,C_13)),k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ r2_hidden(E_49,k5_partfun1(A_11,B_12,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_596,plain,(
    ! [A_219,B_220] :
      ( m1_subset_1('#skF_1'(A_219,B_220),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_219,B_220),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_219,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_219,B_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_20])).

tff(c_917,plain,(
    ! [A_285,B_286] :
      ( m1_subset_1('#skF_1'(A_285,B_286),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_285,B_286),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_285,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_285,B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_596])).

tff(c_12,plain,(
    ! [F_52,A_11,B_12,C_13] :
      ( r2_hidden(F_52,k5_partfun1(A_11,B_12,C_13))
      | ~ r1_partfun1(C_13,F_52)
      | ~ v1_partfun1(F_52,A_11)
      | ~ m1_subset_1(F_52,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(F_52)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34128,plain,(
    ! [A_1309,B_1310,C_1311] :
      ( r2_hidden('#skF_1'(A_1309,B_1310),k5_partfun1('#skF_6','#skF_7',C_1311))
      | ~ r1_partfun1(C_1311,'#skF_1'(A_1309,B_1310))
      | ~ v1_partfun1('#skF_1'(A_1309,B_1310),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1309,B_1310))
      | ~ m1_subset_1(C_1311,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1311)
      | ~ r2_hidden('#skF_1'(A_1309,B_1310),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_1309,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1309,B_1310) ) ),
    inference(resolution,[status(thm)],[c_917,c_12])).

tff(c_34171,plain,(
    ! [A_1317,B_1318,C_1319] :
      ( r2_hidden('#skF_1'(A_1317,B_1318),k5_partfun1('#skF_6','#skF_7',C_1319))
      | ~ r1_partfun1(C_1319,'#skF_1'(A_1317,B_1318))
      | ~ v1_partfun1('#skF_1'(A_1317,B_1318),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1317,B_1318))
      | ~ m1_subset_1(C_1319,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1319)
      | ~ r1_tarski(A_1317,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1317,B_1318) ) ),
    inference(resolution,[status(thm)],[c_86,c_34128])).

tff(c_34193,plain,(
    ! [C_1324,A_1325] :
      ( ~ r1_partfun1(C_1324,'#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7',C_1324)))
      | ~ v1_partfun1('#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7',C_1324)),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7',C_1324)))
      | ~ m1_subset_1(C_1324,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1324)
      | ~ r1_tarski(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1325,k5_partfun1('#skF_6','#skF_7',C_1324)) ) ),
    inference(resolution,[status(thm)],[c_34171,c_4])).

tff(c_34211,plain,(
    ! [A_1325] :
      ( ~ v1_partfun1('#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_9')),'#skF_6')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_9')
      | ~ r1_tarski(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_9'))
      | ~ r1_partfun1('#skF_8','#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_funct_1('#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_relat_1('#skF_1'(A_1325,k5_partfun1('#skF_6','#skF_7','#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_508,c_34193])).

tff(c_34228,plain,(
    ! [A_1326] :
      ( ~ v1_partfun1('#skF_1'(A_1326,k5_partfun1('#skF_6','#skF_7','#skF_9')),'#skF_6')
      | ~ r1_tarski(A_1326,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1326,k5_partfun1('#skF_6','#skF_7','#skF_9'))
      | ~ r1_partfun1('#skF_8','#skF_1'(A_1326,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_funct_1('#skF_1'(A_1326,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_relat_1('#skF_1'(A_1326,k5_partfun1('#skF_6','#skF_7','#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_34211])).

tff(c_34252,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_749,c_34228])).

tff(c_34265,plain,
    ( ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34252])).

tff(c_34266,plain,
    ( ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34265])).

tff(c_34268,plain,(
    ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_34266])).

tff(c_34746,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_629,c_34268])).

tff(c_34750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34746])).

tff(c_34751,plain,
    ( ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_34266])).

tff(c_34753,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_34751])).

tff(c_34756,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_1('#skF_8')
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_2878,c_34753])).

tff(c_34762,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_34756])).

tff(c_34764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34762])).

tff(c_34765,plain,(
    ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_34751])).

tff(c_34769,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_685,c_34765])).

tff(c_34773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:18:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.69/8.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.69/8.77  
% 16.69/8.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.69/8.77  %$ r1_relset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 16.69/8.77  
% 16.69/8.77  %Foreground sorts:
% 16.69/8.77  
% 16.69/8.77  
% 16.69/8.77  %Background operators:
% 16.69/8.77  
% 16.69/8.77  
% 16.69/8.77  %Foreground operators:
% 16.69/8.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.69/8.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.69/8.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.69/8.77  tff(r1_relset_1, type, r1_relset_1: ($i * $i * $i * $i) > $o).
% 16.69/8.77  tff('#skF_7', type, '#skF_7': $i).
% 16.69/8.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 16.69/8.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.69/8.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 16.69/8.77  tff('#skF_6', type, '#skF_6': $i).
% 16.69/8.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 16.69/8.77  tff('#skF_9', type, '#skF_9': $i).
% 16.69/8.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.69/8.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 16.69/8.77  tff('#skF_8', type, '#skF_8': $i).
% 16.69/8.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.69/8.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.69/8.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.69/8.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.69/8.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 16.69/8.77  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 16.69/8.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.69/8.77  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 16.69/8.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.69/8.77  
% 16.69/8.79  tff(f_96, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_relset_1(A, B, D, C) => r1_tarski(k5_partfun1(A, B, C), k5_partfun1(A, B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_2)).
% 16.69/8.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.69/8.79  tff(f_62, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 16.69/8.79  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.69/8.79  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 16.69/8.79  tff(f_82, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => ((r1_partfun1(C, E) & r1_relset_1(A, B, D, C)) => r1_partfun1(D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_partfun1)).
% 16.69/8.79  tff(c_50, plain, (~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.69/8.79  tff(c_63, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.69/8.79  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.69/8.79  tff(c_68, plain, (![A_67]: (r1_tarski(A_67, A_67))), inference(resolution, [status(thm)], [c_63, c_4])).
% 16.69/8.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.69/8.79  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.69/8.79  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.69/8.79  tff(c_83, plain, (![C_72, B_73, A_74]: (r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.69/8.79  tff(c_86, plain, (![A_1, B_2, B_73]: (r2_hidden('#skF_1'(A_1, B_2), B_73) | ~r1_tarski(A_1, B_73) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_83])).
% 16.69/8.79  tff(c_113, plain, (![C_88, A_89, B_90, E_91]: ('#skF_5'(C_88, A_89, B_90, E_91, k5_partfun1(A_89, B_90, C_88))=E_91 | ~r2_hidden(E_91, k5_partfun1(A_89, B_90, C_88)) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_570, plain, (![C_215, A_218, A_216, B_214, B_217]: ('#skF_5'(C_215, A_216, B_214, '#skF_1'(A_218, B_217), k5_partfun1(A_216, B_214, C_215))='#skF_1'(A_218, B_217) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_1(C_215) | ~r1_tarski(A_218, k5_partfun1(A_216, B_214, C_215)) | r1_tarski(A_218, B_217))), inference(resolution, [status(thm)], [c_86, c_113])).
% 16.69/8.79  tff(c_576, plain, (![A_218, B_217]: ('#skF_5'('#skF_8', '#skF_6', '#skF_7', '#skF_1'(A_218, B_217), k5_partfun1('#skF_6', '#skF_7', '#skF_8'))='#skF_1'(A_218, B_217) | ~v1_funct_1('#skF_8') | ~r1_tarski(A_218, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_218, B_217))), inference(resolution, [status(thm)], [c_58, c_570])).
% 16.69/8.79  tff(c_587, plain, (![A_219, B_220]: ('#skF_5'('#skF_8', '#skF_6', '#skF_7', '#skF_1'(A_219, B_220), k5_partfun1('#skF_6', '#skF_7', '#skF_8'))='#skF_1'(A_219, B_220) | ~r1_tarski(A_219, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_219, B_220))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_576])).
% 16.69/8.79  tff(c_96, plain, (![C_78, A_79, B_80, E_81]: (v1_funct_1('#skF_5'(C_78, A_79, B_80, E_81, k5_partfun1(A_79, B_80, C_78))) | ~r2_hidden(E_81, k5_partfun1(A_79, B_80, C_78)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_98, plain, (![E_81]: (v1_funct_1('#skF_5'('#skF_8', '#skF_6', '#skF_7', E_81, k5_partfun1('#skF_6', '#skF_7', '#skF_8'))) | ~r2_hidden(E_81, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_96])).
% 16.69/8.79  tff(c_103, plain, (![E_81]: (v1_funct_1('#skF_5'('#skF_8', '#skF_6', '#skF_7', E_81, k5_partfun1('#skF_6', '#skF_7', '#skF_8'))) | ~r2_hidden(E_81, k5_partfun1('#skF_6', '#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_98])).
% 16.69/8.79  tff(c_673, plain, (![A_232, B_233]: (v1_funct_1('#skF_1'(A_232, B_233)) | ~r2_hidden('#skF_1'(A_232, B_233), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_tarski(A_232, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_232, B_233))), inference(superposition, [status(thm), theory('equality')], [c_587, c_103])).
% 16.69/8.79  tff(c_681, plain, (![B_2]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2)) | ~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(resolution, [status(thm)], [c_6, c_673])).
% 16.69/8.79  tff(c_685, plain, (![B_2]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2)) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_681])).
% 16.69/8.79  tff(c_1059, plain, (![C_303, A_304, B_305, B_306]: ('#skF_5'(C_303, A_304, B_305, '#skF_1'(k5_partfun1(A_304, B_305, C_303), B_306), k5_partfun1(A_304, B_305, C_303))='#skF_1'(k5_partfun1(A_304, B_305, C_303), B_306) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_304, B_305))) | ~v1_funct_1(C_303) | r1_tarski(k5_partfun1(A_304, B_305, C_303), B_306))), inference(resolution, [status(thm)], [c_6, c_113])).
% 16.69/8.79  tff(c_14, plain, (![C_13, A_11, B_12, E_49]: (r1_partfun1(C_13, '#skF_5'(C_13, A_11, B_12, E_49, k5_partfun1(A_11, B_12, C_13))) | ~r2_hidden(E_49, k5_partfun1(A_11, B_12, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_2867, plain, (![C_418, A_419, B_420, B_421]: (r1_partfun1(C_418, '#skF_1'(k5_partfun1(A_419, B_420, C_418), B_421)) | ~r2_hidden('#skF_1'(k5_partfun1(A_419, B_420, C_418), B_421), k5_partfun1(A_419, B_420, C_418)) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))) | ~v1_funct_1(C_418) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))) | ~v1_funct_1(C_418) | r1_tarski(k5_partfun1(A_419, B_420, C_418), B_421))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_14])).
% 16.69/8.79  tff(c_2871, plain, (![C_418, A_419, B_420, B_2]: (r1_partfun1(C_418, '#skF_1'(k5_partfun1(A_419, B_420, C_418), B_2)) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))) | ~v1_funct_1(C_418) | ~r1_tarski(k5_partfun1(A_419, B_420, C_418), k5_partfun1(A_419, B_420, C_418)) | r1_tarski(k5_partfun1(A_419, B_420, C_418), B_2))), inference(resolution, [status(thm)], [c_86, c_2867])).
% 16.69/8.79  tff(c_2878, plain, (![C_418, A_419, B_420, B_2]: (r1_partfun1(C_418, '#skF_1'(k5_partfun1(A_419, B_420, C_418), B_2)) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))) | ~v1_funct_1(C_418) | r1_tarski(k5_partfun1(A_419, B_420, C_418), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2871])).
% 16.69/8.79  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.69/8.79  tff(c_319, plain, (![C_159, A_160, B_161, E_162]: (m1_subset_1('#skF_5'(C_159, A_160, B_161, E_162, k5_partfun1(A_160, B_161, C_159)), k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~r2_hidden(E_162, k5_partfun1(A_160, B_161, C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_8, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.69/8.79  tff(c_332, plain, (![C_159, A_160, B_161, E_162]: (v1_relat_1('#skF_5'(C_159, A_160, B_161, E_162, k5_partfun1(A_160, B_161, C_159))) | ~v1_relat_1(k2_zfmisc_1(A_160, B_161)) | ~r2_hidden(E_162, k5_partfun1(A_160, B_161, C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(C_159))), inference(resolution, [status(thm)], [c_319, c_8])).
% 16.69/8.79  tff(c_344, plain, (![C_163, A_164, B_165, E_166]: (v1_relat_1('#skF_5'(C_163, A_164, B_165, E_166, k5_partfun1(A_164, B_165, C_163))) | ~r2_hidden(E_166, k5_partfun1(A_164, B_165, C_163)) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_1(C_163))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_332])).
% 16.69/8.79  tff(c_348, plain, (![E_166]: (v1_relat_1('#skF_5'('#skF_8', '#skF_6', '#skF_7', E_166, k5_partfun1('#skF_6', '#skF_7', '#skF_8'))) | ~r2_hidden(E_166, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_344])).
% 16.69/8.79  tff(c_354, plain, (![E_166]: (v1_relat_1('#skF_5'('#skF_8', '#skF_6', '#skF_7', E_166, k5_partfun1('#skF_6', '#skF_7', '#skF_8'))) | ~r2_hidden(E_166, k5_partfun1('#skF_6', '#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_348])).
% 16.69/8.79  tff(c_617, plain, (![A_221, B_222]: (v1_relat_1('#skF_1'(A_221, B_222)) | ~r2_hidden('#skF_1'(A_221, B_222), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_tarski(A_221, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_221, B_222))), inference(superposition, [status(thm), theory('equality')], [c_587, c_354])).
% 16.69/8.79  tff(c_625, plain, (![B_2]: (v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2)) | ~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(resolution, [status(thm)], [c_6, c_617])).
% 16.69/8.79  tff(c_629, plain, (![B_2]: (v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2)) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_625])).
% 16.69/8.79  tff(c_16, plain, (![C_13, A_11, B_12, E_49]: (v1_partfun1('#skF_5'(C_13, A_11, B_12, E_49, k5_partfun1(A_11, B_12, C_13)), A_11) | ~r2_hidden(E_49, k5_partfun1(A_11, B_12, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_602, plain, (![A_219, B_220]: (v1_partfun1('#skF_1'(A_219, B_220), '#skF_6') | ~r2_hidden('#skF_1'(A_219, B_220), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8') | ~r1_tarski(A_219, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_219, B_220))), inference(superposition, [status(thm), theory('equality')], [c_587, c_16])).
% 16.69/8.79  tff(c_737, plain, (![A_251, B_252]: (v1_partfun1('#skF_1'(A_251, B_252), '#skF_6') | ~r2_hidden('#skF_1'(A_251, B_252), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_tarski(A_251, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_251, B_252))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_602])).
% 16.69/8.79  tff(c_745, plain, (![B_2]: (v1_partfun1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2), '#skF_6') | ~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(resolution, [status(thm)], [c_6, c_737])).
% 16.69/8.79  tff(c_749, plain, (![B_2]: (v1_partfun1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2), '#skF_6') | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_745])).
% 16.69/8.79  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.69/8.79  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.69/8.79  tff(c_52, plain, (r1_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.69/8.79  tff(c_503, plain, (![C_193, D_196, A_194, E_195, B_197]: (r1_partfun1(D_196, E_195) | ~r1_relset_1(A_194, B_197, D_196, C_193) | ~r1_partfun1(C_193, E_195) | ~v1_funct_1(E_195) | ~v1_relat_1(E_195) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_197))) | ~v1_funct_1(D_196) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_194, B_197))) | ~v1_funct_1(C_193))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.69/8.79  tff(c_505, plain, (![E_195]: (r1_partfun1('#skF_9', E_195) | ~r1_partfun1('#skF_8', E_195) | ~v1_funct_1(E_195) | ~v1_relat_1(E_195) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_503])).
% 16.69/8.79  tff(c_508, plain, (![E_195]: (r1_partfun1('#skF_9', E_195) | ~r1_partfun1('#skF_8', E_195) | ~v1_funct_1(E_195) | ~v1_relat_1(E_195))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_505])).
% 16.69/8.79  tff(c_20, plain, (![C_13, A_11, B_12, E_49]: (m1_subset_1('#skF_5'(C_13, A_11, B_12, E_49, k5_partfun1(A_11, B_12, C_13)), k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~r2_hidden(E_49, k5_partfun1(A_11, B_12, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_596, plain, (![A_219, B_220]: (m1_subset_1('#skF_1'(A_219, B_220), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden('#skF_1'(A_219, B_220), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8') | ~r1_tarski(A_219, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_219, B_220))), inference(superposition, [status(thm), theory('equality')], [c_587, c_20])).
% 16.69/8.79  tff(c_917, plain, (![A_285, B_286]: (m1_subset_1('#skF_1'(A_285, B_286), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden('#skF_1'(A_285, B_286), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_tarski(A_285, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_285, B_286))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_596])).
% 16.69/8.79  tff(c_12, plain, (![F_52, A_11, B_12, C_13]: (r2_hidden(F_52, k5_partfun1(A_11, B_12, C_13)) | ~r1_partfun1(C_13, F_52) | ~v1_partfun1(F_52, A_11) | ~m1_subset_1(F_52, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(F_52) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.69/8.79  tff(c_34128, plain, (![A_1309, B_1310, C_1311]: (r2_hidden('#skF_1'(A_1309, B_1310), k5_partfun1('#skF_6', '#skF_7', C_1311)) | ~r1_partfun1(C_1311, '#skF_1'(A_1309, B_1310)) | ~v1_partfun1('#skF_1'(A_1309, B_1310), '#skF_6') | ~v1_funct_1('#skF_1'(A_1309, B_1310)) | ~m1_subset_1(C_1311, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_1311) | ~r2_hidden('#skF_1'(A_1309, B_1310), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_tarski(A_1309, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1309, B_1310))), inference(resolution, [status(thm)], [c_917, c_12])).
% 16.69/8.79  tff(c_34171, plain, (![A_1317, B_1318, C_1319]: (r2_hidden('#skF_1'(A_1317, B_1318), k5_partfun1('#skF_6', '#skF_7', C_1319)) | ~r1_partfun1(C_1319, '#skF_1'(A_1317, B_1318)) | ~v1_partfun1('#skF_1'(A_1317, B_1318), '#skF_6') | ~v1_funct_1('#skF_1'(A_1317, B_1318)) | ~m1_subset_1(C_1319, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_1319) | ~r1_tarski(A_1317, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1317, B_1318))), inference(resolution, [status(thm)], [c_86, c_34128])).
% 16.69/8.79  tff(c_34193, plain, (![C_1324, A_1325]: (~r1_partfun1(C_1324, '#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', C_1324))) | ~v1_partfun1('#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', C_1324)), '#skF_6') | ~v1_funct_1('#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', C_1324))) | ~m1_subset_1(C_1324, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_1324) | ~r1_tarski(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1325, k5_partfun1('#skF_6', '#skF_7', C_1324)))), inference(resolution, [status(thm)], [c_34171, c_4])).
% 16.69/8.79  tff(c_34211, plain, (![A_1325]: (~v1_partfun1('#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_9')), '#skF_6') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_9') | ~r1_tarski(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_9')) | ~r1_partfun1('#skF_8', '#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(A_1325, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))))), inference(resolution, [status(thm)], [c_508, c_34193])).
% 16.69/8.79  tff(c_34228, plain, (![A_1326]: (~v1_partfun1('#skF_1'(A_1326, k5_partfun1('#skF_6', '#skF_7', '#skF_9')), '#skF_6') | ~r1_tarski(A_1326, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1326, k5_partfun1('#skF_6', '#skF_7', '#skF_9')) | ~r1_partfun1('#skF_8', '#skF_1'(A_1326, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(A_1326, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(A_1326, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_34211])).
% 16.69/8.79  tff(c_34252, plain, (~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_749, c_34228])).
% 16.69/8.79  tff(c_34265, plain, (~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34252])).
% 16.69/8.79  tff(c_34266, plain, (~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_50, c_34265])).
% 16.69/8.79  tff(c_34268, plain, (~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_34266])).
% 16.69/8.79  tff(c_34746, plain, (r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_629, c_34268])).
% 16.69/8.79  tff(c_34750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_34746])).
% 16.69/8.79  tff(c_34751, plain, (~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_34266])).
% 16.69/8.79  tff(c_34753, plain, (~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_34751])).
% 16.69/8.79  tff(c_34756, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8') | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_2878, c_34753])).
% 16.69/8.79  tff(c_34762, plain, (r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_34756])).
% 16.69/8.79  tff(c_34764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_34762])).
% 16.69/8.79  tff(c_34765, plain, (~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_34751])).
% 16.69/8.79  tff(c_34769, plain, (r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_685, c_34765])).
% 16.69/8.79  tff(c_34773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_34769])).
% 16.69/8.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.69/8.79  
% 16.69/8.79  Inference rules
% 16.69/8.79  ----------------------
% 16.69/8.79  #Ref     : 0
% 16.69/8.79  #Sup     : 6367
% 16.69/8.79  #Fact    : 0
% 16.69/8.79  #Define  : 0
% 16.69/8.79  #Split   : 11
% 16.69/8.79  #Chain   : 0
% 16.69/8.80  #Close   : 0
% 16.69/8.80  
% 16.69/8.80  Ordering : KBO
% 16.69/8.80  
% 16.69/8.80  Simplification rules
% 16.69/8.80  ----------------------
% 16.69/8.80  #Subsume      : 745
% 16.69/8.80  #Demod        : 6930
% 16.69/8.80  #Tautology    : 1748
% 16.69/8.80  #SimpNegUnit  : 767
% 16.69/8.80  #BackRed      : 75
% 16.69/8.80  
% 16.69/8.80  #Partial instantiations: 0
% 16.69/8.80  #Strategies tried      : 1
% 16.69/8.80  
% 16.69/8.80  Timing (in seconds)
% 16.69/8.80  ----------------------
% 16.69/8.80  Preprocessing        : 0.33
% 16.69/8.80  Parsing              : 0.16
% 16.69/8.80  CNF conversion       : 0.03
% 16.69/8.80  Main loop            : 7.69
% 16.69/8.80  Inferencing          : 2.37
% 16.69/8.80  Reduction            : 2.12
% 16.69/8.80  Demodulation         : 1.52
% 16.69/8.80  BG Simplification    : 0.27
% 16.69/8.80  Subsumption          : 2.52
% 16.69/8.80  Abstraction          : 0.41
% 16.69/8.80  MUC search           : 0.00
% 16.69/8.80  Cooper               : 0.00
% 16.69/8.80  Total                : 8.06
% 16.69/8.80  Index Insertion      : 0.00
% 16.69/8.80  Index Deletion       : 0.00
% 16.69/8.80  Index Matching       : 0.00
% 16.69/8.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
