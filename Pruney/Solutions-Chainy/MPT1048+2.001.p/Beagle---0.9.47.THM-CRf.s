%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:08 EST 2020

% Result     : Theorem 17.66s
% Output     : CNFRefutation 17.66s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 333 expanded)
%              Number of leaves         :   29 ( 131 expanded)
%              Depth                    :   17
%              Number of atoms          :  239 (1166 expanded)
%              Number of equality atoms :    7 (  36 expanded)
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

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_relset_1(A,B,D,C)
             => r1_tarski(k5_partfun1(A,B,C),k5_partfun1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_partfun1)).

tff(f_57,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_partfun1)).

tff(c_54,plain,(
    ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [D_89,A_90,B_91,C_92] :
      ( v1_funct_1(D_89)
      | ~ r2_hidden(D_89,k5_partfun1(A_90,B_91,C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_117,plain,(
    ! [A_97,B_98,C_99,B_100] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_97,B_98,C_99),B_100))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(C_99)
      | r1_tarski(k5_partfun1(A_97,B_98,C_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_119,plain,(
    ! [B_100] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_100))
      | ~ v1_funct_1('#skF_8')
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_100) ) ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_124,plain,(
    ! [B_100] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_100))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_119])).

tff(c_75,plain,(
    ! [A_76,B_77] :
      ( ~ r2_hidden('#skF_1'(A_76,B_77),B_77)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_82,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_1,B_2,B_80] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_80)
      | ~ r1_tarski(A_1,B_80)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_151,plain,(
    ! [B_112,C_113,E_114,A_115] :
      ( '#skF_5'(B_112,C_113,E_114,k5_partfun1(A_115,B_112,C_113),A_115) = E_114
      | ~ r2_hidden(E_114,k5_partfun1(A_115,B_112,C_113))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_112)))
      | ~ v1_funct_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1685,plain,(
    ! [B_407,C_408,A_409,B_410] :
      ( '#skF_5'(B_407,C_408,'#skF_1'(k5_partfun1(A_409,B_407,C_408),B_410),k5_partfun1(A_409,B_407,C_408),A_409) = '#skF_1'(k5_partfun1(A_409,B_407,C_408),B_410)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_409,B_407)))
      | ~ v1_funct_1(C_408)
      | r1_tarski(k5_partfun1(A_409,B_407,C_408),B_410) ) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_12,plain,(
    ! [C_11,B_10,E_47,A_9] :
      ( r1_partfun1(C_11,'#skF_5'(B_10,C_11,E_47,k5_partfun1(A_9,B_10,C_11),A_9))
      | ~ r2_hidden(E_47,k5_partfun1(A_9,B_10,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8776,plain,(
    ! [C_826,A_827,B_828,B_829] :
      ( r1_partfun1(C_826,'#skF_1'(k5_partfun1(A_827,B_828,C_826),B_829))
      | ~ r2_hidden('#skF_1'(k5_partfun1(A_827,B_828,C_826),B_829),k5_partfun1(A_827,B_828,C_826))
      | ~ m1_subset_1(C_826,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828)))
      | ~ v1_funct_1(C_826)
      | ~ m1_subset_1(C_826,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828)))
      | ~ v1_funct_1(C_826)
      | r1_tarski(k5_partfun1(A_827,B_828,C_826),B_829) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1685,c_12])).

tff(c_8788,plain,(
    ! [C_826,A_827,B_828,B_2] :
      ( r1_partfun1(C_826,'#skF_1'(k5_partfun1(A_827,B_828,C_826),B_2))
      | ~ m1_subset_1(C_826,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828)))
      | ~ v1_funct_1(C_826)
      | ~ r1_tarski(k5_partfun1(A_827,B_828,C_826),k5_partfun1(A_827,B_828,C_826))
      | r1_tarski(k5_partfun1(A_827,B_828,C_826),B_2) ) ),
    inference(resolution,[status(thm)],[c_85,c_8776])).

tff(c_8797,plain,(
    ! [C_826,A_827,B_828,B_2] :
      ( r1_partfun1(C_826,'#skF_1'(k5_partfun1(A_827,B_828,C_826),B_2))
      | ~ m1_subset_1(C_826,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828)))
      | ~ v1_funct_1(C_826)
      | r1_tarski(k5_partfun1(A_827,B_828,C_826),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8788])).

tff(c_108,plain,(
    ! [D_93,A_94,B_95,C_96] :
      ( m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ r2_hidden(D_93,k5_partfun1(A_94,B_95,C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_184,plain,(
    ! [A_134,B_135,C_136,B_137] :
      ( m1_subset_1('#skF_1'(k5_partfun1(A_134,B_135,C_136),B_137),k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(C_136)
      | r1_tarski(k5_partfun1(A_134,B_135,C_136),B_137) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_198,plain,(
    ! [A_138,B_139,C_140,B_141] :
      ( v1_relat_1('#skF_1'(k5_partfun1(A_138,B_139,C_140),B_141))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(C_140)
      | r1_tarski(k5_partfun1(A_138,B_139,C_140),B_141) ) ),
    inference(resolution,[status(thm)],[c_184,c_8])).

tff(c_202,plain,(
    ! [B_141] :
      ( v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_141))
      | ~ v1_funct_1('#skF_8')
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_141) ) ),
    inference(resolution,[status(thm)],[c_62,c_198])).

tff(c_208,plain,(
    ! [B_141] :
      ( v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_141))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_202])).

tff(c_992,plain,(
    ! [A_293,B_292,A_291,C_289,B_290] :
      ( '#skF_5'(B_292,C_289,'#skF_1'(A_291,B_290),k5_partfun1(A_293,B_292,C_289),A_293) = '#skF_1'(A_291,B_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292)))
      | ~ v1_funct_1(C_289)
      | ~ r1_tarski(A_291,k5_partfun1(A_293,B_292,C_289))
      | r1_tarski(A_291,B_290) ) ),
    inference(resolution,[status(thm)],[c_85,c_151])).

tff(c_1004,plain,(
    ! [A_291,B_290] :
      ( '#skF_5'('#skF_7','#skF_8','#skF_1'(A_291,B_290),k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_1'(A_291,B_290)
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_291,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_291,B_290) ) ),
    inference(resolution,[status(thm)],[c_62,c_992])).

tff(c_1018,plain,(
    ! [A_294,B_295] :
      ( '#skF_5'('#skF_7','#skF_8','#skF_1'(A_294,B_295),k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_1'(A_294,B_295)
      | ~ r1_tarski(A_294,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_294,B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1004])).

tff(c_14,plain,(
    ! [B_10,C_11,E_47,A_9] :
      ( v1_partfun1('#skF_5'(B_10,C_11,E_47,k5_partfun1(A_9,B_10,C_11),A_9),A_9)
      | ~ r2_hidden(E_47,k5_partfun1(A_9,B_10,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1033,plain,(
    ! [A_294,B_295] :
      ( v1_partfun1('#skF_1'(A_294,B_295),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_294,B_295),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_294,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_294,B_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_14])).

tff(c_1097,plain,(
    ! [A_303,B_304] :
      ( v1_partfun1('#skF_1'(A_303,B_304),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_303,B_304),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_303,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_303,B_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1033])).

tff(c_1105,plain,(
    ! [B_2] :
      ( v1_partfun1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2),'#skF_6')
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_1109,plain,(
    ! [B_2] :
      ( v1_partfun1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2),'#skF_6')
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1105])).

tff(c_60,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    r1_relset_1('#skF_6','#skF_7','#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_966,plain,(
    ! [D_264,C_263,B_262,A_261,E_265] :
      ( r1_partfun1(D_264,E_265)
      | ~ r1_relset_1(A_261,B_262,D_264,C_263)
      | ~ r1_partfun1(C_263,E_265)
      | ~ v1_funct_1(E_265)
      | ~ v1_relat_1(E_265)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(D_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_968,plain,(
    ! [E_265] :
      ( r1_partfun1('#skF_9',E_265)
      | ~ r1_partfun1('#skF_8',E_265)
      | ~ v1_funct_1(E_265)
      | ~ v1_relat_1(E_265)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_966])).

tff(c_971,plain,(
    ! [E_265] :
      ( r1_partfun1('#skF_9',E_265)
      | ~ r1_partfun1('#skF_8',E_265)
      | ~ v1_funct_1(E_265)
      | ~ v1_relat_1(E_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_968])).

tff(c_214,plain,(
    ! [B_147,A_144,A_148,B_145,C_146] :
      ( m1_subset_1('#skF_1'(A_148,B_147),k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_1(C_146)
      | ~ r1_tarski(A_148,k5_partfun1(A_144,B_145,C_146))
      | r1_tarski(A_148,B_147) ) ),
    inference(resolution,[status(thm)],[c_85,c_108])).

tff(c_218,plain,(
    ! [A_148,B_147] :
      ( m1_subset_1('#skF_1'(A_148,B_147),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_148,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_148,B_147) ) ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_224,plain,(
    ! [A_148,B_147] :
      ( m1_subset_1('#skF_1'(A_148,B_147),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r1_tarski(A_148,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_148,B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_218])).

tff(c_515,plain,(
    ! [F_197,A_198,B_199,C_200] :
      ( r2_hidden(F_197,k5_partfun1(A_198,B_199,C_200))
      | ~ r1_partfun1(C_200,F_197)
      | ~ v1_partfun1(F_197,A_198)
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7956,plain,(
    ! [A_743,B_744,C_745] :
      ( r2_hidden('#skF_1'(A_743,B_744),k5_partfun1('#skF_6','#skF_7',C_745))
      | ~ r1_partfun1(C_745,'#skF_1'(A_743,B_744))
      | ~ v1_partfun1('#skF_1'(A_743,B_744),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_743,B_744))
      | ~ m1_subset_1(C_745,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_745)
      | ~ r1_tarski(A_743,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_743,B_744) ) ),
    inference(resolution,[status(thm)],[c_224,c_515])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25366,plain,(
    ! [C_1514,A_1515] :
      ( ~ r1_partfun1(C_1514,'#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7',C_1514)))
      | ~ v1_partfun1('#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7',C_1514)),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7',C_1514)))
      | ~ m1_subset_1(C_1514,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1514)
      | ~ r1_tarski(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1515,k5_partfun1('#skF_6','#skF_7',C_1514)) ) ),
    inference(resolution,[status(thm)],[c_7956,c_4])).

tff(c_25378,plain,(
    ! [A_1515] :
      ( ~ v1_partfun1('#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_9')),'#skF_6')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_9')
      | ~ r1_tarski(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_9'))
      | ~ r1_partfun1('#skF_8','#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_funct_1('#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_relat_1('#skF_1'(A_1515,k5_partfun1('#skF_6','#skF_7','#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_971,c_25366])).

tff(c_25389,plain,(
    ! [A_1516] :
      ( ~ v1_partfun1('#skF_1'(A_1516,k5_partfun1('#skF_6','#skF_7','#skF_9')),'#skF_6')
      | ~ r1_tarski(A_1516,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1516,k5_partfun1('#skF_6','#skF_7','#skF_9'))
      | ~ r1_partfun1('#skF_8','#skF_1'(A_1516,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_funct_1('#skF_1'(A_1516,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_relat_1('#skF_1'(A_1516,k5_partfun1('#skF_6','#skF_7','#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_25378])).

tff(c_25405,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_1109,c_25389])).

tff(c_25416,plain,
    ( ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_25405])).

tff(c_25417,plain,
    ( ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_25416])).

tff(c_25419,plain,(
    ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_25417])).

tff(c_25422,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_208,c_25419])).

tff(c_25426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_25422])).

tff(c_25427,plain,
    ( ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_25417])).

tff(c_25429,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_25427])).

tff(c_25432,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_1('#skF_8')
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_8797,c_25429])).

tff(c_25438,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_25432])).

tff(c_25440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_25438])).

tff(c_25441,plain,(
    ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_25427])).

tff(c_25445,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_124,c_25441])).

tff(c_25449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_25445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:08:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.66/8.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/8.18  
% 17.66/8.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/8.18  %$ r1_relset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 17.66/8.18  
% 17.66/8.18  %Foreground sorts:
% 17.66/8.18  
% 17.66/8.18  
% 17.66/8.18  %Background operators:
% 17.66/8.18  
% 17.66/8.18  
% 17.66/8.18  %Foreground operators:
% 17.66/8.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.66/8.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.66/8.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.66/8.18  tff(r1_relset_1, type, r1_relset_1: ($i * $i * $i * $i) > $o).
% 17.66/8.18  tff('#skF_7', type, '#skF_7': $i).
% 17.66/8.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 17.66/8.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.66/8.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 17.66/8.18  tff('#skF_6', type, '#skF_6': $i).
% 17.66/8.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 17.66/8.18  tff('#skF_9', type, '#skF_9': $i).
% 17.66/8.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.66/8.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 17.66/8.18  tff('#skF_8', type, '#skF_8': $i).
% 17.66/8.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.66/8.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.66/8.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.66/8.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.66/8.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 17.66/8.18  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 17.66/8.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.66/8.18  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 17.66/8.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.66/8.18  
% 17.66/8.20  tff(f_115, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_relset_1(A, B, D, C) => r1_tarski(k5_partfun1(A, B, C), k5_partfun1(A, B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_2)).
% 17.66/8.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.66/8.20  tff(f_88, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => (v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_partfun1)).
% 17.66/8.20  tff(f_57, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 17.66/8.20  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.66/8.20  tff(f_77, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => ((r1_partfun1(C, E) & r1_relset_1(A, B, D, C)) => r1_partfun1(D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_partfun1)).
% 17.66/8.20  tff(c_54, plain, (~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.66/8.20  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.66/8.20  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.66/8.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.66/8.20  tff(c_99, plain, (![D_89, A_90, B_91, C_92]: (v1_funct_1(D_89) | ~r2_hidden(D_89, k5_partfun1(A_90, B_91, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_88])).
% 17.66/8.20  tff(c_117, plain, (![A_97, B_98, C_99, B_100]: (v1_funct_1('#skF_1'(k5_partfun1(A_97, B_98, C_99), B_100)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(C_99) | r1_tarski(k5_partfun1(A_97, B_98, C_99), B_100))), inference(resolution, [status(thm)], [c_6, c_99])).
% 17.66/8.20  tff(c_119, plain, (![B_100]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_100)) | ~v1_funct_1('#skF_8') | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_100))), inference(resolution, [status(thm)], [c_62, c_117])).
% 17.66/8.20  tff(c_124, plain, (![B_100]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_100)) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_100))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_119])).
% 17.66/8.20  tff(c_75, plain, (![A_76, B_77]: (~r2_hidden('#skF_1'(A_76, B_77), B_77) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.66/8.20  tff(c_80, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_75])).
% 17.66/8.20  tff(c_82, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.66/8.20  tff(c_85, plain, (![A_1, B_2, B_80]: (r2_hidden('#skF_1'(A_1, B_2), B_80) | ~r1_tarski(A_1, B_80) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_82])).
% 17.66/8.20  tff(c_151, plain, (![B_112, C_113, E_114, A_115]: ('#skF_5'(B_112, C_113, E_114, k5_partfun1(A_115, B_112, C_113), A_115)=E_114 | ~r2_hidden(E_114, k5_partfun1(A_115, B_112, C_113)) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_112))) | ~v1_funct_1(C_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.66/8.20  tff(c_1685, plain, (![B_407, C_408, A_409, B_410]: ('#skF_5'(B_407, C_408, '#skF_1'(k5_partfun1(A_409, B_407, C_408), B_410), k5_partfun1(A_409, B_407, C_408), A_409)='#skF_1'(k5_partfun1(A_409, B_407, C_408), B_410) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_409, B_407))) | ~v1_funct_1(C_408) | r1_tarski(k5_partfun1(A_409, B_407, C_408), B_410))), inference(resolution, [status(thm)], [c_6, c_151])).
% 17.66/8.20  tff(c_12, plain, (![C_11, B_10, E_47, A_9]: (r1_partfun1(C_11, '#skF_5'(B_10, C_11, E_47, k5_partfun1(A_9, B_10, C_11), A_9)) | ~r2_hidden(E_47, k5_partfun1(A_9, B_10, C_11)) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.66/8.20  tff(c_8776, plain, (![C_826, A_827, B_828, B_829]: (r1_partfun1(C_826, '#skF_1'(k5_partfun1(A_827, B_828, C_826), B_829)) | ~r2_hidden('#skF_1'(k5_partfun1(A_827, B_828, C_826), B_829), k5_partfun1(A_827, B_828, C_826)) | ~m1_subset_1(C_826, k1_zfmisc_1(k2_zfmisc_1(A_827, B_828))) | ~v1_funct_1(C_826) | ~m1_subset_1(C_826, k1_zfmisc_1(k2_zfmisc_1(A_827, B_828))) | ~v1_funct_1(C_826) | r1_tarski(k5_partfun1(A_827, B_828, C_826), B_829))), inference(superposition, [status(thm), theory('equality')], [c_1685, c_12])).
% 17.66/8.20  tff(c_8788, plain, (![C_826, A_827, B_828, B_2]: (r1_partfun1(C_826, '#skF_1'(k5_partfun1(A_827, B_828, C_826), B_2)) | ~m1_subset_1(C_826, k1_zfmisc_1(k2_zfmisc_1(A_827, B_828))) | ~v1_funct_1(C_826) | ~r1_tarski(k5_partfun1(A_827, B_828, C_826), k5_partfun1(A_827, B_828, C_826)) | r1_tarski(k5_partfun1(A_827, B_828, C_826), B_2))), inference(resolution, [status(thm)], [c_85, c_8776])).
% 17.66/8.20  tff(c_8797, plain, (![C_826, A_827, B_828, B_2]: (r1_partfun1(C_826, '#skF_1'(k5_partfun1(A_827, B_828, C_826), B_2)) | ~m1_subset_1(C_826, k1_zfmisc_1(k2_zfmisc_1(A_827, B_828))) | ~v1_funct_1(C_826) | r1_tarski(k5_partfun1(A_827, B_828, C_826), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8788])).
% 17.66/8.20  tff(c_108, plain, (![D_93, A_94, B_95, C_96]: (m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~r2_hidden(D_93, k5_partfun1(A_94, B_95, C_96)) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_88])).
% 17.66/8.20  tff(c_184, plain, (![A_134, B_135, C_136, B_137]: (m1_subset_1('#skF_1'(k5_partfun1(A_134, B_135, C_136), B_137), k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(C_136) | r1_tarski(k5_partfun1(A_134, B_135, C_136), B_137))), inference(resolution, [status(thm)], [c_6, c_108])).
% 17.66/8.20  tff(c_8, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 17.66/8.20  tff(c_198, plain, (![A_138, B_139, C_140, B_141]: (v1_relat_1('#skF_1'(k5_partfun1(A_138, B_139, C_140), B_141)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(C_140) | r1_tarski(k5_partfun1(A_138, B_139, C_140), B_141))), inference(resolution, [status(thm)], [c_184, c_8])).
% 17.66/8.20  tff(c_202, plain, (![B_141]: (v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_141)) | ~v1_funct_1('#skF_8') | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_141))), inference(resolution, [status(thm)], [c_62, c_198])).
% 17.66/8.20  tff(c_208, plain, (![B_141]: (v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_141)) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_141))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_202])).
% 17.66/8.20  tff(c_992, plain, (![A_293, B_292, A_291, C_289, B_290]: ('#skF_5'(B_292, C_289, '#skF_1'(A_291, B_290), k5_partfun1(A_293, B_292, C_289), A_293)='#skF_1'(A_291, B_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))) | ~v1_funct_1(C_289) | ~r1_tarski(A_291, k5_partfun1(A_293, B_292, C_289)) | r1_tarski(A_291, B_290))), inference(resolution, [status(thm)], [c_85, c_151])).
% 17.66/8.20  tff(c_1004, plain, (![A_291, B_290]: ('#skF_5'('#skF_7', '#skF_8', '#skF_1'(A_291, B_290), k5_partfun1('#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_1'(A_291, B_290) | ~v1_funct_1('#skF_8') | ~r1_tarski(A_291, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_291, B_290))), inference(resolution, [status(thm)], [c_62, c_992])).
% 17.66/8.20  tff(c_1018, plain, (![A_294, B_295]: ('#skF_5'('#skF_7', '#skF_8', '#skF_1'(A_294, B_295), k5_partfun1('#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_1'(A_294, B_295) | ~r1_tarski(A_294, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_294, B_295))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1004])).
% 17.66/8.20  tff(c_14, plain, (![B_10, C_11, E_47, A_9]: (v1_partfun1('#skF_5'(B_10, C_11, E_47, k5_partfun1(A_9, B_10, C_11), A_9), A_9) | ~r2_hidden(E_47, k5_partfun1(A_9, B_10, C_11)) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.66/8.20  tff(c_1033, plain, (![A_294, B_295]: (v1_partfun1('#skF_1'(A_294, B_295), '#skF_6') | ~r2_hidden('#skF_1'(A_294, B_295), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8') | ~r1_tarski(A_294, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_294, B_295))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_14])).
% 17.66/8.20  tff(c_1097, plain, (![A_303, B_304]: (v1_partfun1('#skF_1'(A_303, B_304), '#skF_6') | ~r2_hidden('#skF_1'(A_303, B_304), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_tarski(A_303, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_303, B_304))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1033])).
% 17.66/8.20  tff(c_1105, plain, (![B_2]: (v1_partfun1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2), '#skF_6') | ~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(resolution, [status(thm)], [c_6, c_1097])).
% 17.66/8.20  tff(c_1109, plain, (![B_2]: (v1_partfun1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2), '#skF_6') | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1105])).
% 17.66/8.20  tff(c_60, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.66/8.20  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.66/8.20  tff(c_56, plain, (r1_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.66/8.20  tff(c_966, plain, (![D_264, C_263, B_262, A_261, E_265]: (r1_partfun1(D_264, E_265) | ~r1_relset_1(A_261, B_262, D_264, C_263) | ~r1_partfun1(C_263, E_265) | ~v1_funct_1(E_265) | ~v1_relat_1(E_265) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(D_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.66/8.20  tff(c_968, plain, (![E_265]: (r1_partfun1('#skF_9', E_265) | ~r1_partfun1('#skF_8', E_265) | ~v1_funct_1(E_265) | ~v1_relat_1(E_265) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_966])).
% 17.66/8.20  tff(c_971, plain, (![E_265]: (r1_partfun1('#skF_9', E_265) | ~r1_partfun1('#skF_8', E_265) | ~v1_funct_1(E_265) | ~v1_relat_1(E_265))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_968])).
% 17.66/8.20  tff(c_214, plain, (![B_147, A_144, A_148, B_145, C_146]: (m1_subset_1('#skF_1'(A_148, B_147), k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_1(C_146) | ~r1_tarski(A_148, k5_partfun1(A_144, B_145, C_146)) | r1_tarski(A_148, B_147))), inference(resolution, [status(thm)], [c_85, c_108])).
% 17.66/8.20  tff(c_218, plain, (![A_148, B_147]: (m1_subset_1('#skF_1'(A_148, B_147), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8') | ~r1_tarski(A_148, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_148, B_147))), inference(resolution, [status(thm)], [c_62, c_214])).
% 17.66/8.20  tff(c_224, plain, (![A_148, B_147]: (m1_subset_1('#skF_1'(A_148, B_147), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r1_tarski(A_148, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_148, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_218])).
% 17.66/8.20  tff(c_515, plain, (![F_197, A_198, B_199, C_200]: (r2_hidden(F_197, k5_partfun1(A_198, B_199, C_200)) | ~r1_partfun1(C_200, F_197) | ~v1_partfun1(F_197, A_198) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(F_197) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.66/8.20  tff(c_7956, plain, (![A_743, B_744, C_745]: (r2_hidden('#skF_1'(A_743, B_744), k5_partfun1('#skF_6', '#skF_7', C_745)) | ~r1_partfun1(C_745, '#skF_1'(A_743, B_744)) | ~v1_partfun1('#skF_1'(A_743, B_744), '#skF_6') | ~v1_funct_1('#skF_1'(A_743, B_744)) | ~m1_subset_1(C_745, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_745) | ~r1_tarski(A_743, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_743, B_744))), inference(resolution, [status(thm)], [c_224, c_515])).
% 17.66/8.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.66/8.20  tff(c_25366, plain, (![C_1514, A_1515]: (~r1_partfun1(C_1514, '#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', C_1514))) | ~v1_partfun1('#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', C_1514)), '#skF_6') | ~v1_funct_1('#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', C_1514))) | ~m1_subset_1(C_1514, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_1514) | ~r1_tarski(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1515, k5_partfun1('#skF_6', '#skF_7', C_1514)))), inference(resolution, [status(thm)], [c_7956, c_4])).
% 17.66/8.20  tff(c_25378, plain, (![A_1515]: (~v1_partfun1('#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_9')), '#skF_6') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_9') | ~r1_tarski(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_9')) | ~r1_partfun1('#skF_8', '#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(A_1515, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))))), inference(resolution, [status(thm)], [c_971, c_25366])).
% 17.66/8.20  tff(c_25389, plain, (![A_1516]: (~v1_partfun1('#skF_1'(A_1516, k5_partfun1('#skF_6', '#skF_7', '#skF_9')), '#skF_6') | ~r1_tarski(A_1516, k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | r1_tarski(A_1516, k5_partfun1('#skF_6', '#skF_7', '#skF_9')) | ~r1_partfun1('#skF_8', '#skF_1'(A_1516, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(A_1516, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(A_1516, k5_partfun1('#skF_6', '#skF_7', '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_25378])).
% 17.66/8.20  tff(c_25405, plain, (~r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_1109, c_25389])).
% 17.66/8.20  tff(c_25416, plain, (~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_25405])).
% 17.66/8.20  tff(c_25417, plain, (~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_54, c_25416])).
% 17.66/8.20  tff(c_25419, plain, (~v1_relat_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_25417])).
% 17.66/8.20  tff(c_25422, plain, (r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_208, c_25419])).
% 17.66/8.20  tff(c_25426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_25422])).
% 17.66/8.20  tff(c_25427, plain, (~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))) | ~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_25417])).
% 17.66/8.20  tff(c_25429, plain, (~r1_partfun1('#skF_8', '#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_25427])).
% 17.66/8.20  tff(c_25432, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_8') | r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_8797, c_25429])).
% 17.66/8.20  tff(c_25438, plain, (r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_25432])).
% 17.66/8.20  tff(c_25440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_25438])).
% 17.66/8.20  tff(c_25441, plain, (~v1_funct_1('#skF_1'(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_25427])).
% 17.66/8.20  tff(c_25445, plain, (r1_tarski(k5_partfun1('#skF_6', '#skF_7', '#skF_8'), k5_partfun1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_124, c_25441])).
% 17.66/8.20  tff(c_25449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_25445])).
% 17.66/8.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/8.20  
% 17.66/8.20  Inference rules
% 17.66/8.20  ----------------------
% 17.66/8.20  #Ref     : 0
% 17.66/8.20  #Sup     : 6184
% 17.66/8.20  #Fact    : 0
% 17.66/8.20  #Define  : 0
% 17.66/8.20  #Split   : 21
% 17.66/8.20  #Chain   : 0
% 17.66/8.20  #Close   : 0
% 17.66/8.20  
% 17.66/8.20  Ordering : KBO
% 17.66/8.20  
% 17.66/8.20  Simplification rules
% 17.66/8.20  ----------------------
% 17.66/8.20  #Subsume      : 395
% 17.66/8.20  #Demod        : 2494
% 17.66/8.20  #Tautology    : 592
% 17.66/8.20  #SimpNegUnit  : 251
% 17.66/8.20  #BackRed      : 35
% 17.66/8.20  
% 17.66/8.20  #Partial instantiations: 0
% 17.66/8.20  #Strategies tried      : 1
% 17.66/8.20  
% 17.66/8.20  Timing (in seconds)
% 17.66/8.20  ----------------------
% 17.66/8.20  Preprocessing        : 0.34
% 17.66/8.20  Parsing              : 0.17
% 17.66/8.20  CNF conversion       : 0.03
% 17.66/8.20  Main loop            : 7.08
% 17.66/8.20  Inferencing          : 1.73
% 17.66/8.20  Reduction            : 1.75
% 17.66/8.20  Demodulation         : 1.22
% 17.66/8.20  BG Simplification    : 0.22
% 17.66/8.20  Subsumption          : 2.80
% 17.66/8.20  Abstraction          : 0.38
% 17.66/8.20  MUC search           : 0.00
% 17.66/8.20  Cooper               : 0.00
% 17.66/8.20  Total                : 7.46
% 17.66/8.20  Index Insertion      : 0.00
% 17.66/8.20  Index Deletion       : 0.00
% 17.66/8.20  Index Matching       : 0.00
% 17.66/8.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
