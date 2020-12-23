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
% DateTime   : Thu Dec  3 10:08:32 EST 2020

% Result     : Theorem 16.43s
% Output     : CNFRefutation 16.70s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 382 expanded)
%              Number of leaves         :   39 ( 143 expanded)
%              Depth                    :   11
%              Number of atoms          :  316 (1100 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_15 > #skF_10 > #skF_14 > #skF_13 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_60,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_84,plain,(
    ! [C_180,A_181,B_182] :
      ( v1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_88,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_19501,plain,(
    ! [A_1235,B_1236,C_1237] :
      ( r2_hidden('#skF_9'(A_1235,B_1236,C_1237),k1_relat_1(C_1237))
      | ~ r2_hidden(A_1235,k9_relat_1(C_1237,B_1236))
      | ~ v1_relat_1(C_1237) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_19033,plain,(
    ! [C_1186,A_1187] :
      ( r2_hidden(k4_tarski(C_1186,'#skF_8'(A_1187,k1_relat_1(A_1187),C_1186)),A_1187)
      | ~ r2_hidden(C_1186,k1_relat_1(A_1187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18250,plain,(
    ! [A_1088,B_1089,C_1090,D_1091] :
      ( k7_relset_1(A_1088,B_1089,C_1090,D_1091) = k9_relat_1(C_1090,D_1091)
      | ~ m1_subset_1(C_1090,k1_zfmisc_1(k2_zfmisc_1(A_1088,B_1089))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18257,plain,(
    ! [D_1091] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_1091) = k9_relat_1('#skF_13',D_1091) ),
    inference(resolution,[status(thm)],[c_60,c_18250])).

tff(c_17753,plain,(
    ! [A_1004,B_1005,C_1006] :
      ( r2_hidden('#skF_9'(A_1004,B_1005,C_1006),k1_relat_1(C_1006))
      | ~ r2_hidden(A_1004,k9_relat_1(C_1006,B_1005))
      | ~ v1_relat_1(C_1006) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17305,plain,(
    ! [C_961,A_962] :
      ( r2_hidden(k4_tarski(C_961,'#skF_8'(A_962,k1_relat_1(A_962),C_961)),A_962)
      | ~ r2_hidden(C_961,k1_relat_1(A_962)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16731,plain,(
    ! [A_887,B_888,C_889,D_890] :
      ( k7_relset_1(A_887,B_888,C_889,D_890) = k9_relat_1(C_889,D_890)
      | ~ m1_subset_1(C_889,k1_zfmisc_1(k2_zfmisc_1(A_887,B_888))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16738,plain,(
    ! [D_890] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_890) = k9_relat_1('#skF_13',D_890) ),
    inference(resolution,[status(thm)],[c_60,c_16731])).

tff(c_1399,plain,(
    ! [A_366,B_367,C_368,D_369] :
      ( k7_relset_1(A_366,B_367,C_368,D_369) = k9_relat_1(C_368,D_369)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1406,plain,(
    ! [D_369] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_369) = k9_relat_1('#skF_13',D_369) ),
    inference(resolution,[status(thm)],[c_60,c_1399])).

tff(c_82,plain,
    ( r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11'))
    | m1_subset_1('#skF_15','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_94,plain,(
    m1_subset_1('#skF_15','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_74,plain,
    ( r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11'))
    | r2_hidden('#skF_15','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_106,plain,(
    r2_hidden('#skF_15','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_78,plain,
    ( r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11'))
    | r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_115,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_433,plain,(
    ! [A_248,B_249,C_250,D_251] :
      ( k7_relset_1(A_248,B_249,C_250,D_251) = k9_relat_1(C_250,D_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_436,plain,(
    ! [D_251] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_251) = k9_relat_1('#skF_13',D_251) ),
    inference(resolution,[status(thm)],[c_60,c_433])).

tff(c_68,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12')
      | ~ r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_475,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_68])).

tff(c_476,plain,(
    ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_898,plain,(
    ! [D_297,A_298,B_299,E_300] :
      ( r2_hidden(D_297,k9_relat_1(A_298,B_299))
      | ~ r2_hidden(E_300,B_299)
      | ~ r2_hidden(k4_tarski(E_300,D_297),A_298)
      | ~ v1_relat_1(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_974,plain,(
    ! [D_301,A_302] :
      ( r2_hidden(D_301,k9_relat_1(A_302,'#skF_11'))
      | ~ r2_hidden(k4_tarski('#skF_15',D_301),A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(resolution,[status(thm)],[c_106,c_898])).

tff(c_1021,plain,
    ( r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_115,c_974])).

tff(c_1039,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1021])).

tff(c_1041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_1039])).

tff(c_1055,plain,(
    ! [F_303] :
      ( ~ r2_hidden(F_303,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_303,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_303,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_1058,plain,
    ( ~ r2_hidden('#skF_15','#skF_11')
    | ~ m1_subset_1('#skF_15','#skF_12') ),
    inference(resolution,[status(thm)],[c_115,c_1055])).

tff(c_1065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_106,c_1058])).

tff(c_1066,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1408,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_1066])).

tff(c_1261,plain,(
    ! [A_343,B_344,C_345] :
      ( r2_hidden('#skF_9'(A_343,B_344,C_345),k1_relat_1(C_345))
      | ~ r2_hidden(A_343,k9_relat_1(C_345,B_344))
      | ~ v1_relat_1(C_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1101,plain,(
    ! [C_318,A_319] :
      ( r2_hidden(k4_tarski(C_318,'#skF_8'(A_319,k1_relat_1(A_319),C_318)),A_319)
      | ~ r2_hidden(C_318,k1_relat_1(A_319)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,(
    ! [C_188,B_189,A_190] :
      ( ~ v1_xboole_0(C_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(C_188))
      | ~ r2_hidden(A_190,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_190] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(A_190,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_60,c_101])).

tff(c_105,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_111,plain,(
    ! [A_191,C_192,B_193] :
      ( m1_subset_1(A_191,C_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(C_192))
      | ~ r2_hidden(A_191,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [A_191] :
      ( m1_subset_1(A_191,k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(A_191,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_60,c_111])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [C_185,A_186,D_187] :
      ( r2_hidden(C_185,k1_relat_1(A_186))
      | ~ r2_hidden(k4_tarski(C_185,D_187),A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1088,plain,(
    ! [C_313,B_314,D_315] :
      ( r2_hidden(C_313,k1_relat_1(B_314))
      | v1_xboole_0(B_314)
      | ~ m1_subset_1(k4_tarski(C_313,D_315),B_314) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_1091,plain,(
    ! [C_313,D_315] :
      ( r2_hidden(C_313,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(k4_tarski(C_313,D_315),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_114,c_1088])).

tff(c_1094,plain,(
    ! [C_313,D_315] :
      ( r2_hidden(C_313,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | ~ r2_hidden(k4_tarski(C_313,D_315),'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1091])).

tff(c_1135,plain,(
    ! [C_323] :
      ( r2_hidden(C_323,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | ~ r2_hidden(C_323,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_1101,c_1094])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1120,plain,(
    ! [C_318,C_3,D_4] :
      ( r2_hidden(C_318,C_3)
      | ~ r2_hidden(C_318,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_1101,c_6])).

tff(c_1146,plain,(
    ! [C_323] :
      ( r2_hidden(C_323,'#skF_12')
      | ~ r2_hidden(C_323,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_1135,c_1120])).

tff(c_1267,plain,(
    ! [A_343,B_344] :
      ( r2_hidden('#skF_9'(A_343,B_344,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_343,k9_relat_1('#skF_13',B_344))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1261,c_1146])).

tff(c_1281,plain,(
    ! [A_346,B_347] :
      ( r2_hidden('#skF_9'(A_346,B_347,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_346,k9_relat_1('#skF_13',B_347)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1267])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1288,plain,(
    ! [A_346,B_347] :
      ( m1_subset_1('#skF_9'(A_346,B_347,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_346,k9_relat_1('#skF_13',B_347)) ) ),
    inference(resolution,[status(thm)],[c_1281,c_8])).

tff(c_1426,plain,(
    m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_1408,c_1288])).

tff(c_48,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_9'(A_76,B_77,C_78),B_77)
      | ~ r2_hidden(A_76,k9_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1485,plain,(
    ! [A_378,B_379,C_380] :
      ( r2_hidden(k4_tarski('#skF_9'(A_378,B_379,C_380),A_378),C_380)
      | ~ r2_hidden(A_378,k9_relat_1(C_380,B_379))
      | ~ v1_relat_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1067,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12')
      | r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1329,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1067,c_76])).

tff(c_1492,plain,(
    ! [B_379] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_379,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_379,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_379))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1485,c_1329])).

tff(c_16384,plain,(
    ! [B_820] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_820,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_820,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_820)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1492])).

tff(c_16388,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_48,c_16384])).

tff(c_16395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1408,c_1426,c_16388])).

tff(c_16396,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_16742,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16738,c_16396])).

tff(c_16627,plain,(
    ! [A_871,B_872,C_873] :
      ( r2_hidden('#skF_9'(A_871,B_872,C_873),k1_relat_1(C_873))
      | ~ r2_hidden(A_871,k9_relat_1(C_873,B_872))
      | ~ v1_relat_1(C_873) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16477,plain,(
    ! [C_850,A_851] :
      ( r2_hidden(k4_tarski(C_850,'#skF_8'(A_851,k1_relat_1(A_851),C_850)),A_851)
      | ~ r2_hidden(C_850,k1_relat_1(A_851)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16414,plain,(
    ! [A_825,C_826,B_827] :
      ( m1_subset_1(A_825,C_826)
      | ~ m1_subset_1(B_827,k1_zfmisc_1(C_826))
      | ~ r2_hidden(A_825,B_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16417,plain,(
    ! [A_825] :
      ( m1_subset_1(A_825,k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(A_825,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_60,c_16414])).

tff(c_16429,plain,(
    ! [C_836,B_837,D_838] :
      ( r2_hidden(C_836,k1_relat_1(B_837))
      | v1_xboole_0(B_837)
      | ~ m1_subset_1(k4_tarski(C_836,D_838),B_837) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_16432,plain,(
    ! [C_836,D_838] :
      ( r2_hidden(C_836,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(k4_tarski(C_836,D_838),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_16417,c_16429])).

tff(c_16435,plain,(
    ! [C_836,D_838] :
      ( r2_hidden(C_836,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | ~ r2_hidden(k4_tarski(C_836,D_838),'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_16432])).

tff(c_16519,plain,(
    ! [C_855] :
      ( r2_hidden(C_855,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | ~ r2_hidden(C_855,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_16477,c_16435])).

tff(c_16500,plain,(
    ! [C_850,C_3,D_4] :
      ( r2_hidden(C_850,C_3)
      | ~ r2_hidden(C_850,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_16477,c_6])).

tff(c_16532,plain,(
    ! [C_855] :
      ( r2_hidden(C_855,'#skF_12')
      | ~ r2_hidden(C_855,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_16519,c_16500])).

tff(c_16631,plain,(
    ! [A_871,B_872] :
      ( r2_hidden('#skF_9'(A_871,B_872,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_871,k9_relat_1('#skF_13',B_872))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_16627,c_16532])).

tff(c_16648,plain,(
    ! [A_875,B_876] :
      ( r2_hidden('#skF_9'(A_875,B_876,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_875,k9_relat_1('#skF_13',B_876)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16631])).

tff(c_16655,plain,(
    ! [A_875,B_876] :
      ( m1_subset_1('#skF_9'(A_875,B_876,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_875,k9_relat_1('#skF_13',B_876)) ) ),
    inference(resolution,[status(thm)],[c_16648,c_8])).

tff(c_16762,plain,(
    m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_16742,c_16655])).

tff(c_17103,plain,(
    ! [A_932,B_933,C_934] :
      ( r2_hidden(k4_tarski('#skF_9'(A_932,B_933,C_934),A_932),C_934)
      | ~ r2_hidden(A_932,k9_relat_1(C_934,B_933))
      | ~ v1_relat_1(C_934) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16397,plain,(
    ~ r2_hidden('#skF_15','#skF_11') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12')
      | r2_hidden('#skF_15','#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16458,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_16397,c_72])).

tff(c_17138,plain,(
    ! [B_933] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_933,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_933,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_933))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_17103,c_16458])).

tff(c_17237,plain,(
    ! [B_939] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_939,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_939,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_939)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_17138])).

tff(c_17241,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_48,c_17237])).

tff(c_17248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16742,c_16762,c_17241])).

tff(c_17249,plain,(
    ! [A_190] : ~ r2_hidden(A_190,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_17331,plain,(
    ! [C_961] : ~ r2_hidden(C_961,k1_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_17305,c_17249])).

tff(c_17809,plain,(
    ! [A_1004,B_1005] :
      ( ~ r2_hidden(A_1004,k9_relat_1('#skF_13',B_1005))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_17753,c_17331])).

tff(c_17828,plain,(
    ! [A_1004,B_1005] : ~ r2_hidden(A_1004,k9_relat_1('#skF_13',B_1005)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_17809])).

tff(c_17934,plain,(
    ! [A_1018,B_1019,C_1020,D_1021] :
      ( k7_relset_1(A_1018,B_1019,C_1020,D_1021) = k9_relat_1(C_1020,D_1021)
      | ~ m1_subset_1(C_1020,k1_zfmisc_1(k2_zfmisc_1(A_1018,B_1019))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_17937,plain,(
    ! [D_1021] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_1021) = k9_relat_1('#skF_13',D_1021) ),
    inference(resolution,[status(thm)],[c_60,c_17934])).

tff(c_17273,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_17249,c_78])).

tff(c_17939,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17937,c_17273])).

tff(c_17941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17828,c_17939])).

tff(c_17942,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_18260,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18257,c_17942])).

tff(c_18145,plain,(
    ! [A_1070,B_1071,C_1072] :
      ( r2_hidden('#skF_9'(A_1070,B_1071,C_1072),k1_relat_1(C_1072))
      | ~ r2_hidden(A_1070,k9_relat_1(C_1072,B_1071))
      | ~ v1_relat_1(C_1072) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18023,plain,(
    ! [C_1056,A_1057] :
      ( r2_hidden(k4_tarski(C_1056,'#skF_8'(A_1057,k1_relat_1(A_1057),C_1056)),A_1057)
      | ~ r2_hidden(C_1056,k1_relat_1(A_1057)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17949,plain,(
    ! [C_1022,B_1023,A_1024] :
      ( ~ v1_xboole_0(C_1022)
      | ~ m1_subset_1(B_1023,k1_zfmisc_1(C_1022))
      | ~ r2_hidden(A_1024,B_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_17952,plain,(
    ! [A_1024] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(A_1024,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_60,c_17949])).

tff(c_17953,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_17952])).

tff(c_17965,plain,(
    ! [A_1032,C_1033,B_1034] :
      ( m1_subset_1(A_1032,C_1033)
      | ~ m1_subset_1(B_1034,k1_zfmisc_1(C_1033))
      | ~ r2_hidden(A_1032,B_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17968,plain,(
    ! [A_1032] :
      ( m1_subset_1(A_1032,k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(A_1032,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_60,c_17965])).

tff(c_17954,plain,(
    ! [C_1025,A_1026,D_1027] :
      ( r2_hidden(C_1025,k1_relat_1(A_1026))
      | ~ r2_hidden(k4_tarski(C_1025,D_1027),A_1026) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17976,plain,(
    ! [C_1040,B_1041,D_1042] :
      ( r2_hidden(C_1040,k1_relat_1(B_1041))
      | v1_xboole_0(B_1041)
      | ~ m1_subset_1(k4_tarski(C_1040,D_1042),B_1041) ) ),
    inference(resolution,[status(thm)],[c_10,c_17954])).

tff(c_17979,plain,(
    ! [C_1040,D_1042] :
      ( r2_hidden(C_1040,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
      | ~ r2_hidden(k4_tarski(C_1040,D_1042),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_17968,c_17976])).

tff(c_17982,plain,(
    ! [C_1040,D_1042] :
      ( r2_hidden(C_1040,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | ~ r2_hidden(k4_tarski(C_1040,D_1042),'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_17953,c_17979])).

tff(c_18065,plain,(
    ! [C_1061] :
      ( r2_hidden(C_1061,k1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')))
      | ~ r2_hidden(C_1061,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_18023,c_17982])).

tff(c_18046,plain,(
    ! [C_1056,C_3,D_4] :
      ( r2_hidden(C_1056,C_3)
      | ~ r2_hidden(C_1056,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_18023,c_6])).

tff(c_18078,plain,(
    ! [C_1061] :
      ( r2_hidden(C_1061,'#skF_12')
      | ~ r2_hidden(C_1061,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_18065,c_18046])).

tff(c_18149,plain,(
    ! [A_1070,B_1071] :
      ( r2_hidden('#skF_9'(A_1070,B_1071,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_1070,k9_relat_1('#skF_13',B_1071))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_18145,c_18078])).

tff(c_18165,plain,(
    ! [A_1073,B_1074] :
      ( r2_hidden('#skF_9'(A_1073,B_1074,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_1073,k9_relat_1('#skF_13',B_1074)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_18149])).

tff(c_18172,plain,(
    ! [A_1073,B_1074] :
      ( m1_subset_1('#skF_9'(A_1073,B_1074,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_1073,k9_relat_1('#skF_13',B_1074)) ) ),
    inference(resolution,[status(thm)],[c_18165,c_8])).

tff(c_18280,plain,(
    m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_18260,c_18172])).

tff(c_18314,plain,(
    ! [A_1097,B_1098,C_1099] :
      ( r2_hidden(k4_tarski('#skF_9'(A_1097,B_1098,C_1099),A_1097),C_1099)
      | ~ r2_hidden(A_1097,k9_relat_1(C_1099,B_1098))
      | ~ v1_relat_1(C_1099) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17943,plain,(
    ~ m1_subset_1('#skF_15','#skF_12') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_80,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12')
      | m1_subset_1('#skF_15','#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18098,plain,(
    ! [F_177] :
      ( ~ r2_hidden(F_177,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_177,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_177,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_17943,c_80])).

tff(c_18325,plain,(
    ! [B_1098] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_1098,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_1098,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_1098))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_18314,c_18098])).

tff(c_18988,plain,(
    ! [B_1166] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_1166,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_1166,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_1166)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_18325])).

tff(c_18992,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_48,c_18988])).

tff(c_18999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_18260,c_18280,c_18992])).

tff(c_19000,plain,(
    ! [A_1024] : ~ r2_hidden(A_1024,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_17952])).

tff(c_19055,plain,(
    ! [C_1186] : ~ r2_hidden(C_1186,k1_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_19033,c_19000])).

tff(c_19555,plain,(
    ! [A_1235,B_1236] :
      ( ~ r2_hidden(A_1235,k9_relat_1('#skF_13',B_1236))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_19501,c_19055])).

tff(c_19574,plain,(
    ! [A_1235,B_1236] : ~ r2_hidden(A_1235,k9_relat_1('#skF_13',B_1236)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_19555])).

tff(c_19372,plain,(
    ! [A_1220,B_1221,C_1222,D_1223] :
      ( k7_relset_1(A_1220,B_1221,C_1222,D_1223) = k9_relat_1(C_1222,D_1223)
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(k2_zfmisc_1(A_1220,B_1221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_19375,plain,(
    ! [D_1223] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_1223) = k9_relat_1('#skF_13',D_1223) ),
    inference(resolution,[status(thm)],[c_60,c_19372])).

tff(c_19377,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19375,c_17942])).

tff(c_19577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19574,c_19377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.43/7.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.59/7.06  
% 16.59/7.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.59/7.07  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_15 > #skF_10 > #skF_14 > #skF_13 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12
% 16.59/7.07  
% 16.59/7.07  %Foreground sorts:
% 16.59/7.07  
% 16.59/7.07  
% 16.59/7.07  %Background operators:
% 16.59/7.07  
% 16.59/7.07  
% 16.59/7.07  %Foreground operators:
% 16.59/7.07  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.59/7.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.59/7.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.59/7.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.59/7.07  tff('#skF_11', type, '#skF_11': $i).
% 16.59/7.07  tff('#skF_15', type, '#skF_15': $i).
% 16.59/7.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.59/7.07  tff('#skF_10', type, '#skF_10': $i).
% 16.59/7.07  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 16.59/7.07  tff('#skF_14', type, '#skF_14': $i).
% 16.59/7.07  tff('#skF_13', type, '#skF_13': $i).
% 16.59/7.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.59/7.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.59/7.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.59/7.07  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 16.59/7.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 16.59/7.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.59/7.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.59/7.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.59/7.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.59/7.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.59/7.07  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 16.59/7.07  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.59/7.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.59/7.07  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.59/7.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.59/7.07  tff('#skF_12', type, '#skF_12': $i).
% 16.59/7.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.59/7.07  
% 16.70/7.11  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 16.70/7.11  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.70/7.11  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 16.70/7.11  tff(f_75, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 16.70/7.11  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 16.70/7.11  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 16.70/7.11  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 16.70/7.11  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 16.70/7.11  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 16.70/7.11  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 16.70/7.11  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 16.70/7.11  tff(c_60, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_84, plain, (![C_180, A_181, B_182]: (v1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.70/7.11  tff(c_88, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_60, c_84])).
% 16.70/7.11  tff(c_19501, plain, (![A_1235, B_1236, C_1237]: (r2_hidden('#skF_9'(A_1235, B_1236, C_1237), k1_relat_1(C_1237)) | ~r2_hidden(A_1235, k9_relat_1(C_1237, B_1236)) | ~v1_relat_1(C_1237))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_19033, plain, (![C_1186, A_1187]: (r2_hidden(k4_tarski(C_1186, '#skF_8'(A_1187, k1_relat_1(A_1187), C_1186)), A_1187) | ~r2_hidden(C_1186, k1_relat_1(A_1187)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_18250, plain, (![A_1088, B_1089, C_1090, D_1091]: (k7_relset_1(A_1088, B_1089, C_1090, D_1091)=k9_relat_1(C_1090, D_1091) | ~m1_subset_1(C_1090, k1_zfmisc_1(k2_zfmisc_1(A_1088, B_1089))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.70/7.11  tff(c_18257, plain, (![D_1091]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_1091)=k9_relat_1('#skF_13', D_1091))), inference(resolution, [status(thm)], [c_60, c_18250])).
% 16.70/7.11  tff(c_17753, plain, (![A_1004, B_1005, C_1006]: (r2_hidden('#skF_9'(A_1004, B_1005, C_1006), k1_relat_1(C_1006)) | ~r2_hidden(A_1004, k9_relat_1(C_1006, B_1005)) | ~v1_relat_1(C_1006))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_17305, plain, (![C_961, A_962]: (r2_hidden(k4_tarski(C_961, '#skF_8'(A_962, k1_relat_1(A_962), C_961)), A_962) | ~r2_hidden(C_961, k1_relat_1(A_962)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_16731, plain, (![A_887, B_888, C_889, D_890]: (k7_relset_1(A_887, B_888, C_889, D_890)=k9_relat_1(C_889, D_890) | ~m1_subset_1(C_889, k1_zfmisc_1(k2_zfmisc_1(A_887, B_888))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.70/7.11  tff(c_16738, plain, (![D_890]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_890)=k9_relat_1('#skF_13', D_890))), inference(resolution, [status(thm)], [c_60, c_16731])).
% 16.70/7.11  tff(c_1399, plain, (![A_366, B_367, C_368, D_369]: (k7_relset_1(A_366, B_367, C_368, D_369)=k9_relat_1(C_368, D_369) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.70/7.11  tff(c_1406, plain, (![D_369]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_369)=k9_relat_1('#skF_13', D_369))), inference(resolution, [status(thm)], [c_60, c_1399])).
% 16.70/7.11  tff(c_82, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')) | m1_subset_1('#skF_15', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_94, plain, (m1_subset_1('#skF_15', '#skF_12')), inference(splitLeft, [status(thm)], [c_82])).
% 16.70/7.11  tff(c_74, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')) | r2_hidden('#skF_15', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_106, plain, (r2_hidden('#skF_15', '#skF_11')), inference(splitLeft, [status(thm)], [c_74])).
% 16.70/7.11  tff(c_78, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')) | r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_115, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13')), inference(splitLeft, [status(thm)], [c_78])).
% 16.70/7.11  tff(c_433, plain, (![A_248, B_249, C_250, D_251]: (k7_relset_1(A_248, B_249, C_250, D_251)=k9_relat_1(C_250, D_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.70/7.11  tff(c_436, plain, (![D_251]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_251)=k9_relat_1('#skF_13', D_251))), inference(resolution, [status(thm)], [c_60, c_433])).
% 16.70/7.11  tff(c_68, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12') | ~r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_475, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_68])).
% 16.70/7.11  tff(c_476, plain, (~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(splitLeft, [status(thm)], [c_475])).
% 16.70/7.11  tff(c_898, plain, (![D_297, A_298, B_299, E_300]: (r2_hidden(D_297, k9_relat_1(A_298, B_299)) | ~r2_hidden(E_300, B_299) | ~r2_hidden(k4_tarski(E_300, D_297), A_298) | ~v1_relat_1(A_298))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.70/7.11  tff(c_974, plain, (![D_301, A_302]: (r2_hidden(D_301, k9_relat_1(A_302, '#skF_11')) | ~r2_hidden(k4_tarski('#skF_15', D_301), A_302) | ~v1_relat_1(A_302))), inference(resolution, [status(thm)], [c_106, c_898])).
% 16.70/7.11  tff(c_1021, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_115, c_974])).
% 16.70/7.11  tff(c_1039, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1021])).
% 16.70/7.11  tff(c_1041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_1039])).
% 16.70/7.11  tff(c_1055, plain, (![F_303]: (~r2_hidden(F_303, '#skF_11') | ~r2_hidden(k4_tarski(F_303, '#skF_14'), '#skF_13') | ~m1_subset_1(F_303, '#skF_12'))), inference(splitRight, [status(thm)], [c_475])).
% 16.70/7.11  tff(c_1058, plain, (~r2_hidden('#skF_15', '#skF_11') | ~m1_subset_1('#skF_15', '#skF_12')), inference(resolution, [status(thm)], [c_115, c_1055])).
% 16.70/7.11  tff(c_1065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_106, c_1058])).
% 16.70/7.11  tff(c_1066, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_78])).
% 16.70/7.11  tff(c_1408, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_1066])).
% 16.70/7.11  tff(c_1261, plain, (![A_343, B_344, C_345]: (r2_hidden('#skF_9'(A_343, B_344, C_345), k1_relat_1(C_345)) | ~r2_hidden(A_343, k9_relat_1(C_345, B_344)) | ~v1_relat_1(C_345))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_1101, plain, (![C_318, A_319]: (r2_hidden(k4_tarski(C_318, '#skF_8'(A_319, k1_relat_1(A_319), C_318)), A_319) | ~r2_hidden(C_318, k1_relat_1(A_319)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_101, plain, (![C_188, B_189, A_190]: (~v1_xboole_0(C_188) | ~m1_subset_1(B_189, k1_zfmisc_1(C_188)) | ~r2_hidden(A_190, B_189))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.70/7.11  tff(c_104, plain, (![A_190]: (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(A_190, '#skF_13'))), inference(resolution, [status(thm)], [c_60, c_101])).
% 16.70/7.11  tff(c_105, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(splitLeft, [status(thm)], [c_104])).
% 16.70/7.11  tff(c_111, plain, (![A_191, C_192, B_193]: (m1_subset_1(A_191, C_192) | ~m1_subset_1(B_193, k1_zfmisc_1(C_192)) | ~r2_hidden(A_191, B_193))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.70/7.11  tff(c_114, plain, (![A_191]: (m1_subset_1(A_191, k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(A_191, '#skF_13'))), inference(resolution, [status(thm)], [c_60, c_111])).
% 16.70/7.11  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.70/7.11  tff(c_95, plain, (![C_185, A_186, D_187]: (r2_hidden(C_185, k1_relat_1(A_186)) | ~r2_hidden(k4_tarski(C_185, D_187), A_186))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_1088, plain, (![C_313, B_314, D_315]: (r2_hidden(C_313, k1_relat_1(B_314)) | v1_xboole_0(B_314) | ~m1_subset_1(k4_tarski(C_313, D_315), B_314))), inference(resolution, [status(thm)], [c_10, c_95])).
% 16.70/7.11  tff(c_1091, plain, (![C_313, D_315]: (r2_hidden(C_313, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(k4_tarski(C_313, D_315), '#skF_13'))), inference(resolution, [status(thm)], [c_114, c_1088])).
% 16.70/7.11  tff(c_1094, plain, (![C_313, D_315]: (r2_hidden(C_313, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | ~r2_hidden(k4_tarski(C_313, D_315), '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_105, c_1091])).
% 16.70/7.11  tff(c_1135, plain, (![C_323]: (r2_hidden(C_323, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | ~r2_hidden(C_323, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_1101, c_1094])).
% 16.70/7.11  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.70/7.11  tff(c_1120, plain, (![C_318, C_3, D_4]: (r2_hidden(C_318, C_3) | ~r2_hidden(C_318, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_1101, c_6])).
% 16.70/7.11  tff(c_1146, plain, (![C_323]: (r2_hidden(C_323, '#skF_12') | ~r2_hidden(C_323, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_1135, c_1120])).
% 16.70/7.11  tff(c_1267, plain, (![A_343, B_344]: (r2_hidden('#skF_9'(A_343, B_344, '#skF_13'), '#skF_12') | ~r2_hidden(A_343, k9_relat_1('#skF_13', B_344)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1261, c_1146])).
% 16.70/7.11  tff(c_1281, plain, (![A_346, B_347]: (r2_hidden('#skF_9'(A_346, B_347, '#skF_13'), '#skF_12') | ~r2_hidden(A_346, k9_relat_1('#skF_13', B_347)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1267])).
% 16.70/7.11  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.70/7.11  tff(c_1288, plain, (![A_346, B_347]: (m1_subset_1('#skF_9'(A_346, B_347, '#skF_13'), '#skF_12') | ~r2_hidden(A_346, k9_relat_1('#skF_13', B_347)))), inference(resolution, [status(thm)], [c_1281, c_8])).
% 16.70/7.11  tff(c_1426, plain, (m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_1408, c_1288])).
% 16.70/7.11  tff(c_48, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_9'(A_76, B_77, C_78), B_77) | ~r2_hidden(A_76, k9_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_1485, plain, (![A_378, B_379, C_380]: (r2_hidden(k4_tarski('#skF_9'(A_378, B_379, C_380), A_378), C_380) | ~r2_hidden(A_378, k9_relat_1(C_380, B_379)) | ~v1_relat_1(C_380))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_1067, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13')), inference(splitRight, [status(thm)], [c_78])).
% 16.70/7.11  tff(c_76, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12') | r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_1329, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1067, c_76])).
% 16.70/7.11  tff(c_1492, plain, (![B_379]: (~r2_hidden('#skF_9'('#skF_14', B_379, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_379, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_379)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1485, c_1329])).
% 16.70/7.11  tff(c_16384, plain, (![B_820]: (~r2_hidden('#skF_9'('#skF_14', B_820, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_820, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_820)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1492])).
% 16.70/7.11  tff(c_16388, plain, (~m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_48, c_16384])).
% 16.70/7.11  tff(c_16395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1408, c_1426, c_16388])).
% 16.70/7.11  tff(c_16396, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_74])).
% 16.70/7.11  tff(c_16742, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_16738, c_16396])).
% 16.70/7.11  tff(c_16627, plain, (![A_871, B_872, C_873]: (r2_hidden('#skF_9'(A_871, B_872, C_873), k1_relat_1(C_873)) | ~r2_hidden(A_871, k9_relat_1(C_873, B_872)) | ~v1_relat_1(C_873))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_16477, plain, (![C_850, A_851]: (r2_hidden(k4_tarski(C_850, '#skF_8'(A_851, k1_relat_1(A_851), C_850)), A_851) | ~r2_hidden(C_850, k1_relat_1(A_851)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_16414, plain, (![A_825, C_826, B_827]: (m1_subset_1(A_825, C_826) | ~m1_subset_1(B_827, k1_zfmisc_1(C_826)) | ~r2_hidden(A_825, B_827))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.70/7.11  tff(c_16417, plain, (![A_825]: (m1_subset_1(A_825, k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(A_825, '#skF_13'))), inference(resolution, [status(thm)], [c_60, c_16414])).
% 16.70/7.11  tff(c_16429, plain, (![C_836, B_837, D_838]: (r2_hidden(C_836, k1_relat_1(B_837)) | v1_xboole_0(B_837) | ~m1_subset_1(k4_tarski(C_836, D_838), B_837))), inference(resolution, [status(thm)], [c_10, c_95])).
% 16.70/7.11  tff(c_16432, plain, (![C_836, D_838]: (r2_hidden(C_836, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(k4_tarski(C_836, D_838), '#skF_13'))), inference(resolution, [status(thm)], [c_16417, c_16429])).
% 16.70/7.11  tff(c_16435, plain, (![C_836, D_838]: (r2_hidden(C_836, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | ~r2_hidden(k4_tarski(C_836, D_838), '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_105, c_16432])).
% 16.70/7.11  tff(c_16519, plain, (![C_855]: (r2_hidden(C_855, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | ~r2_hidden(C_855, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_16477, c_16435])).
% 16.70/7.11  tff(c_16500, plain, (![C_850, C_3, D_4]: (r2_hidden(C_850, C_3) | ~r2_hidden(C_850, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_16477, c_6])).
% 16.70/7.11  tff(c_16532, plain, (![C_855]: (r2_hidden(C_855, '#skF_12') | ~r2_hidden(C_855, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_16519, c_16500])).
% 16.70/7.11  tff(c_16631, plain, (![A_871, B_872]: (r2_hidden('#skF_9'(A_871, B_872, '#skF_13'), '#skF_12') | ~r2_hidden(A_871, k9_relat_1('#skF_13', B_872)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_16627, c_16532])).
% 16.70/7.11  tff(c_16648, plain, (![A_875, B_876]: (r2_hidden('#skF_9'(A_875, B_876, '#skF_13'), '#skF_12') | ~r2_hidden(A_875, k9_relat_1('#skF_13', B_876)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16631])).
% 16.70/7.11  tff(c_16655, plain, (![A_875, B_876]: (m1_subset_1('#skF_9'(A_875, B_876, '#skF_13'), '#skF_12') | ~r2_hidden(A_875, k9_relat_1('#skF_13', B_876)))), inference(resolution, [status(thm)], [c_16648, c_8])).
% 16.70/7.11  tff(c_16762, plain, (m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_16742, c_16655])).
% 16.70/7.11  tff(c_17103, plain, (![A_932, B_933, C_934]: (r2_hidden(k4_tarski('#skF_9'(A_932, B_933, C_934), A_932), C_934) | ~r2_hidden(A_932, k9_relat_1(C_934, B_933)) | ~v1_relat_1(C_934))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_16397, plain, (~r2_hidden('#skF_15', '#skF_11')), inference(splitRight, [status(thm)], [c_74])).
% 16.70/7.11  tff(c_72, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12') | r2_hidden('#skF_15', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_16458, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_16397, c_72])).
% 16.70/7.11  tff(c_17138, plain, (![B_933]: (~r2_hidden('#skF_9'('#skF_14', B_933, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_933, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_933)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_17103, c_16458])).
% 16.70/7.11  tff(c_17237, plain, (![B_939]: (~r2_hidden('#skF_9'('#skF_14', B_939, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_939, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_939)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_17138])).
% 16.70/7.11  tff(c_17241, plain, (~m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_48, c_17237])).
% 16.70/7.11  tff(c_17248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_16742, c_16762, c_17241])).
% 16.70/7.11  tff(c_17249, plain, (![A_190]: (~r2_hidden(A_190, '#skF_13'))), inference(splitRight, [status(thm)], [c_104])).
% 16.70/7.11  tff(c_17331, plain, (![C_961]: (~r2_hidden(C_961, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_17305, c_17249])).
% 16.70/7.11  tff(c_17809, plain, (![A_1004, B_1005]: (~r2_hidden(A_1004, k9_relat_1('#skF_13', B_1005)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_17753, c_17331])).
% 16.70/7.11  tff(c_17828, plain, (![A_1004, B_1005]: (~r2_hidden(A_1004, k9_relat_1('#skF_13', B_1005)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_17809])).
% 16.70/7.11  tff(c_17934, plain, (![A_1018, B_1019, C_1020, D_1021]: (k7_relset_1(A_1018, B_1019, C_1020, D_1021)=k9_relat_1(C_1020, D_1021) | ~m1_subset_1(C_1020, k1_zfmisc_1(k2_zfmisc_1(A_1018, B_1019))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.70/7.11  tff(c_17937, plain, (![D_1021]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_1021)=k9_relat_1('#skF_13', D_1021))), inference(resolution, [status(thm)], [c_60, c_17934])).
% 16.70/7.11  tff(c_17273, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_17249, c_78])).
% 16.70/7.11  tff(c_17939, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_17937, c_17273])).
% 16.70/7.11  tff(c_17941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17828, c_17939])).
% 16.70/7.11  tff(c_17942, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_82])).
% 16.70/7.11  tff(c_18260, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_18257, c_17942])).
% 16.70/7.11  tff(c_18145, plain, (![A_1070, B_1071, C_1072]: (r2_hidden('#skF_9'(A_1070, B_1071, C_1072), k1_relat_1(C_1072)) | ~r2_hidden(A_1070, k9_relat_1(C_1072, B_1071)) | ~v1_relat_1(C_1072))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_18023, plain, (![C_1056, A_1057]: (r2_hidden(k4_tarski(C_1056, '#skF_8'(A_1057, k1_relat_1(A_1057), C_1056)), A_1057) | ~r2_hidden(C_1056, k1_relat_1(A_1057)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_17949, plain, (![C_1022, B_1023, A_1024]: (~v1_xboole_0(C_1022) | ~m1_subset_1(B_1023, k1_zfmisc_1(C_1022)) | ~r2_hidden(A_1024, B_1023))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.70/7.11  tff(c_17952, plain, (![A_1024]: (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(A_1024, '#skF_13'))), inference(resolution, [status(thm)], [c_60, c_17949])).
% 16.70/7.11  tff(c_17953, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(splitLeft, [status(thm)], [c_17952])).
% 16.70/7.11  tff(c_17965, plain, (![A_1032, C_1033, B_1034]: (m1_subset_1(A_1032, C_1033) | ~m1_subset_1(B_1034, k1_zfmisc_1(C_1033)) | ~r2_hidden(A_1032, B_1034))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.70/7.11  tff(c_17968, plain, (![A_1032]: (m1_subset_1(A_1032, k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(A_1032, '#skF_13'))), inference(resolution, [status(thm)], [c_60, c_17965])).
% 16.70/7.11  tff(c_17954, plain, (![C_1025, A_1026, D_1027]: (r2_hidden(C_1025, k1_relat_1(A_1026)) | ~r2_hidden(k4_tarski(C_1025, D_1027), A_1026))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.70/7.11  tff(c_17976, plain, (![C_1040, B_1041, D_1042]: (r2_hidden(C_1040, k1_relat_1(B_1041)) | v1_xboole_0(B_1041) | ~m1_subset_1(k4_tarski(C_1040, D_1042), B_1041))), inference(resolution, [status(thm)], [c_10, c_17954])).
% 16.70/7.11  tff(c_17979, plain, (![C_1040, D_1042]: (r2_hidden(C_1040, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | ~r2_hidden(k4_tarski(C_1040, D_1042), '#skF_13'))), inference(resolution, [status(thm)], [c_17968, c_17976])).
% 16.70/7.11  tff(c_17982, plain, (![C_1040, D_1042]: (r2_hidden(C_1040, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | ~r2_hidden(k4_tarski(C_1040, D_1042), '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_17953, c_17979])).
% 16.70/7.11  tff(c_18065, plain, (![C_1061]: (r2_hidden(C_1061, k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))) | ~r2_hidden(C_1061, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_18023, c_17982])).
% 16.70/7.11  tff(c_18046, plain, (![C_1056, C_3, D_4]: (r2_hidden(C_1056, C_3) | ~r2_hidden(C_1056, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_18023, c_6])).
% 16.70/7.11  tff(c_18078, plain, (![C_1061]: (r2_hidden(C_1061, '#skF_12') | ~r2_hidden(C_1061, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_18065, c_18046])).
% 16.70/7.11  tff(c_18149, plain, (![A_1070, B_1071]: (r2_hidden('#skF_9'(A_1070, B_1071, '#skF_13'), '#skF_12') | ~r2_hidden(A_1070, k9_relat_1('#skF_13', B_1071)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_18145, c_18078])).
% 16.70/7.11  tff(c_18165, plain, (![A_1073, B_1074]: (r2_hidden('#skF_9'(A_1073, B_1074, '#skF_13'), '#skF_12') | ~r2_hidden(A_1073, k9_relat_1('#skF_13', B_1074)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_18149])).
% 16.70/7.11  tff(c_18172, plain, (![A_1073, B_1074]: (m1_subset_1('#skF_9'(A_1073, B_1074, '#skF_13'), '#skF_12') | ~r2_hidden(A_1073, k9_relat_1('#skF_13', B_1074)))), inference(resolution, [status(thm)], [c_18165, c_8])).
% 16.70/7.11  tff(c_18280, plain, (m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_18260, c_18172])).
% 16.70/7.11  tff(c_18314, plain, (![A_1097, B_1098, C_1099]: (r2_hidden(k4_tarski('#skF_9'(A_1097, B_1098, C_1099), A_1097), C_1099) | ~r2_hidden(A_1097, k9_relat_1(C_1099, B_1098)) | ~v1_relat_1(C_1099))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.70/7.11  tff(c_17943, plain, (~m1_subset_1('#skF_15', '#skF_12')), inference(splitRight, [status(thm)], [c_82])).
% 16.70/7.11  tff(c_80, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12') | m1_subset_1('#skF_15', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.70/7.11  tff(c_18098, plain, (![F_177]: (~r2_hidden(F_177, '#skF_11') | ~r2_hidden(k4_tarski(F_177, '#skF_14'), '#skF_13') | ~m1_subset_1(F_177, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_17943, c_80])).
% 16.70/7.11  tff(c_18325, plain, (![B_1098]: (~r2_hidden('#skF_9'('#skF_14', B_1098, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_1098, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_1098)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_18314, c_18098])).
% 16.70/7.11  tff(c_18988, plain, (![B_1166]: (~r2_hidden('#skF_9'('#skF_14', B_1166, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_1166, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_1166)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_18325])).
% 16.70/7.11  tff(c_18992, plain, (~m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_48, c_18988])).
% 16.70/7.11  tff(c_18999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_18260, c_18280, c_18992])).
% 16.70/7.11  tff(c_19000, plain, (![A_1024]: (~r2_hidden(A_1024, '#skF_13'))), inference(splitRight, [status(thm)], [c_17952])).
% 16.70/7.11  tff(c_19055, plain, (![C_1186]: (~r2_hidden(C_1186, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_19033, c_19000])).
% 16.70/7.11  tff(c_19555, plain, (![A_1235, B_1236]: (~r2_hidden(A_1235, k9_relat_1('#skF_13', B_1236)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_19501, c_19055])).
% 16.70/7.11  tff(c_19574, plain, (![A_1235, B_1236]: (~r2_hidden(A_1235, k9_relat_1('#skF_13', B_1236)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_19555])).
% 16.70/7.11  tff(c_19372, plain, (![A_1220, B_1221, C_1222, D_1223]: (k7_relset_1(A_1220, B_1221, C_1222, D_1223)=k9_relat_1(C_1222, D_1223) | ~m1_subset_1(C_1222, k1_zfmisc_1(k2_zfmisc_1(A_1220, B_1221))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.70/7.11  tff(c_19375, plain, (![D_1223]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_1223)=k9_relat_1('#skF_13', D_1223))), inference(resolution, [status(thm)], [c_60, c_19372])).
% 16.70/7.11  tff(c_19377, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_19375, c_17942])).
% 16.70/7.11  tff(c_19577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19574, c_19377])).
% 16.70/7.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.70/7.11  
% 16.70/7.11  Inference rules
% 16.70/7.11  ----------------------
% 16.70/7.11  #Ref     : 0
% 16.70/7.11  #Sup     : 4757
% 16.70/7.11  #Fact    : 0
% 16.70/7.11  #Define  : 0
% 16.70/7.11  #Split   : 33
% 16.70/7.11  #Chain   : 0
% 16.70/7.11  #Close   : 0
% 16.70/7.11  
% 16.70/7.11  Ordering : KBO
% 16.70/7.11  
% 16.70/7.11  Simplification rules
% 16.70/7.11  ----------------------
% 16.70/7.11  #Subsume      : 202
% 16.70/7.11  #Demod        : 151
% 16.70/7.11  #Tautology    : 145
% 16.70/7.11  #SimpNegUnit  : 40
% 16.70/7.11  #BackRed      : 27
% 16.70/7.11  
% 16.70/7.11  #Partial instantiations: 0
% 16.70/7.11  #Strategies tried      : 1
% 16.70/7.11  
% 16.70/7.11  Timing (in seconds)
% 16.70/7.11  ----------------------
% 16.70/7.12  Preprocessing        : 0.55
% 16.70/7.12  Parsing              : 0.26
% 16.70/7.12  CNF conversion       : 0.06
% 16.70/7.12  Main loop            : 5.60
% 16.70/7.12  Inferencing          : 1.39
% 16.70/7.12  Reduction            : 1.35
% 16.70/7.12  Demodulation         : 0.88
% 16.70/7.12  BG Simplification    : 0.22
% 16.70/7.12  Subsumption          : 2.11
% 16.70/7.12  Abstraction          : 0.24
% 16.70/7.12  MUC search           : 0.00
% 16.70/7.12  Cooper               : 0.00
% 16.70/7.12  Total                : 6.24
% 16.70/7.12  Index Insertion      : 0.00
% 16.70/7.12  Index Deletion       : 0.00
% 16.70/7.12  Index Matching       : 0.00
% 16.70/7.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
