%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:36 EST 2020

% Result     : Theorem 9.75s
% Output     : CNFRefutation 9.75s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 148 expanded)
%              Number of leaves         :   39 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  154 ( 261 expanded)
%              Number of equality atoms :   42 (  95 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > #skF_11 > #skF_6 > #skF_4 > #skF_8 > #skF_12 > #skF_2 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A] : k1_wellord2(k1_tarski(A)) = k1_tarski(k4_tarski(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord2)).

tff(c_32,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,(
    ! [A_97,B_98] : k1_enumset1(A_97,A_97,B_98) = k2_tarski(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_150,plain,(
    ! [B_101,A_102] : r2_hidden(B_101,k2_tarski(A_102,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_10])).

tff(c_153,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_150])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_83] : v1_relat_1(k1_wellord2(A_83)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_94,plain,(
    ! [C_81,D_82,A_75] :
      ( r2_hidden(k4_tarski(C_81,D_82),k1_wellord2(A_75))
      | ~ r1_tarski(C_81,D_82)
      | ~ r2_hidden(D_82,A_75)
      | ~ r2_hidden(C_81,A_75)
      | ~ v1_relat_1(k1_wellord2(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_104,plain,(
    ! [C_81,D_82,A_75] :
      ( r2_hidden(k4_tarski(C_81,D_82),k1_wellord2(A_75))
      | ~ r1_tarski(C_81,D_82)
      | ~ r2_hidden(D_82,A_75)
      | ~ r2_hidden(C_81,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94])).

tff(c_324,plain,(
    ! [A_134,B_135,C_136] : k2_zfmisc_1(k2_tarski(A_134,B_135),k1_tarski(C_136)) = k2_tarski(k4_tarski(A_134,C_136),k4_tarski(B_135,C_136)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_346,plain,(
    ! [B_135,C_136] : k2_zfmisc_1(k2_tarski(B_135,B_135),k1_tarski(C_136)) = k1_tarski(k4_tarski(B_135,C_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_32])).

tff(c_365,plain,(
    ! [B_135,C_136] : k2_zfmisc_1(k1_tarski(B_135),k1_tarski(C_136)) = k1_tarski(k4_tarski(B_135,C_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_346])).

tff(c_92,plain,(
    ! [A_75] :
      ( k3_relat_1(k1_wellord2(A_75)) = A_75
      | ~ v1_relat_1(k1_wellord2(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_106,plain,(
    ! [A_75] : k3_relat_1(k1_wellord2(A_75)) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92])).

tff(c_652,plain,(
    ! [A_170,B_171] :
      ( r2_hidden(k4_tarski('#skF_9'(A_170,B_171),'#skF_10'(A_170,B_171)),A_170)
      | r1_tarski(A_170,B_171)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    ! [B_73,C_74,A_72] :
      ( r2_hidden(B_73,k3_relat_1(C_74))
      | ~ r2_hidden(k4_tarski(A_72,B_73),C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_712,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_10'(A_176,B_177),k3_relat_1(A_176))
      | r1_tarski(A_176,B_177)
      | ~ v1_relat_1(A_176) ) ),
    inference(resolution,[status(thm)],[c_652,c_76])).

tff(c_715,plain,(
    ! [A_75,B_177] :
      ( r2_hidden('#skF_10'(k1_wellord2(A_75),B_177),A_75)
      | r1_tarski(k1_wellord2(A_75),B_177)
      | ~ v1_relat_1(k1_wellord2(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_712])).

tff(c_717,plain,(
    ! [A_75,B_177] :
      ( r2_hidden('#skF_10'(k1_wellord2(A_75),B_177),A_75)
      | r1_tarski(k1_wellord2(A_75),B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_715])).

tff(c_38,plain,(
    ! [E_48,F_49,A_16,B_17] :
      ( r2_hidden(k4_tarski(E_48,F_49),k2_zfmisc_1(A_16,B_17))
      | ~ r2_hidden(F_49,B_17)
      | ~ r2_hidden(E_48,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ! [A_72,C_74,B_73] :
      ( r2_hidden(A_72,k3_relat_1(C_74))
      | ~ r2_hidden(k4_tarski(A_72,B_73),C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_686,plain,(
    ! [A_172,B_173] :
      ( r2_hidden('#skF_9'(A_172,B_173),k3_relat_1(A_172))
      | r1_tarski(A_172,B_173)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_652,c_78])).

tff(c_689,plain,(
    ! [A_75,B_173] :
      ( r2_hidden('#skF_9'(k1_wellord2(A_75),B_173),A_75)
      | r1_tarski(k1_wellord2(A_75),B_173)
      | ~ v1_relat_1(k1_wellord2(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_686])).

tff(c_691,plain,(
    ! [A_75,B_173] :
      ( r2_hidden('#skF_9'(k1_wellord2(A_75),B_173),A_75)
      | r1_tarski(k1_wellord2(A_75),B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_689])).

tff(c_568,plain,(
    ! [E_158,F_159,A_160,B_161] :
      ( r2_hidden(k4_tarski(E_158,F_159),k2_zfmisc_1(A_160,B_161))
      | ~ r2_hidden(F_159,B_161)
      | ~ r2_hidden(E_158,A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1793,plain,(
    ! [E_301,F_302,B_303,C_304] :
      ( r2_hidden(k4_tarski(E_301,F_302),k1_tarski(k4_tarski(B_303,C_304)))
      | ~ r2_hidden(F_302,k1_tarski(C_304))
      | ~ r2_hidden(E_301,k1_tarski(B_303)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_568])).

tff(c_34,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_267,plain,(
    ! [E_121,C_122,B_123,A_124] :
      ( E_121 = C_122
      | E_121 = B_123
      | E_121 = A_124
      | ~ r2_hidden(E_121,k1_enumset1(A_124,B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_286,plain,(
    ! [E_125,B_126,A_127] :
      ( E_125 = B_126
      | E_125 = A_127
      | E_125 = A_127
      | ~ r2_hidden(E_125,k2_tarski(A_127,B_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_267])).

tff(c_295,plain,(
    ! [E_125,A_10] :
      ( E_125 = A_10
      | E_125 = A_10
      | E_125 = A_10
      | ~ r2_hidden(E_125,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_286])).

tff(c_1823,plain,(
    ! [E_305,F_306,B_307,C_308] :
      ( k4_tarski(E_305,F_306) = k4_tarski(B_307,C_308)
      | ~ r2_hidden(F_306,k1_tarski(C_308))
      | ~ r2_hidden(E_305,k1_tarski(B_307)) ) ),
    inference(resolution,[status(thm)],[c_1793,c_295])).

tff(c_1870,plain,(
    ! [E_309,A_310,B_311] :
      ( k4_tarski(E_309,A_310) = k4_tarski(B_311,A_310)
      | ~ r2_hidden(E_309,k1_tarski(B_311)) ) ),
    inference(resolution,[status(thm)],[c_153,c_1823])).

tff(c_2084,plain,(
    ! [B_319,B_320,A_321] :
      ( k4_tarski('#skF_9'(k1_wellord2(k1_tarski(B_319)),B_320),A_321) = k4_tarski(B_319,A_321)
      | r1_tarski(k1_wellord2(k1_tarski(B_319)),B_320) ) ),
    inference(resolution,[status(thm)],[c_691,c_1870])).

tff(c_72,plain,(
    ! [A_55,B_65] :
      ( ~ r2_hidden(k4_tarski('#skF_9'(A_55,B_65),'#skF_10'(A_55,B_65)),B_65)
      | r1_tarski(A_55,B_65)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2179,plain,(
    ! [B_319,B_320] :
      ( ~ r2_hidden(k4_tarski(B_319,'#skF_10'(k1_wellord2(k1_tarski(B_319)),B_320)),B_320)
      | r1_tarski(k1_wellord2(k1_tarski(B_319)),B_320)
      | ~ v1_relat_1(k1_wellord2(k1_tarski(B_319)))
      | r1_tarski(k1_wellord2(k1_tarski(B_319)),B_320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_72])).

tff(c_2228,plain,(
    ! [B_322,B_323] :
      ( ~ r2_hidden(k4_tarski(B_322,'#skF_10'(k1_wellord2(k1_tarski(B_322)),B_323)),B_323)
      | r1_tarski(k1_wellord2(k1_tarski(B_322)),B_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2179])).

tff(c_9451,plain,(
    ! [E_711,A_712,B_713] :
      ( r1_tarski(k1_wellord2(k1_tarski(E_711)),k2_zfmisc_1(A_712,B_713))
      | ~ r2_hidden('#skF_10'(k1_wellord2(k1_tarski(E_711)),k2_zfmisc_1(A_712,B_713)),B_713)
      | ~ r2_hidden(E_711,A_712) ) ),
    inference(resolution,[status(thm)],[c_38,c_2228])).

tff(c_9586,plain,(
    ! [E_714,A_715] :
      ( ~ r2_hidden(E_714,A_715)
      | r1_tarski(k1_wellord2(k1_tarski(E_714)),k2_zfmisc_1(A_715,k1_tarski(E_714))) ) ),
    inference(resolution,[status(thm)],[c_717,c_9451])).

tff(c_9608,plain,(
    ! [C_716,B_717] :
      ( ~ r2_hidden(C_716,k1_tarski(B_717))
      | r1_tarski(k1_wellord2(k1_tarski(C_716)),k1_tarski(k4_tarski(B_717,C_716))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_9586])).

tff(c_64,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_50,B_51] :
      ( k1_tarski(A_50) = B_51
      | ~ r1_tarski(B_51,k1_tarski(A_50))
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_64,c_172])).

tff(c_9916,plain,(
    ! [C_749,B_750] :
      ( k1_wellord2(k1_tarski(C_749)) = k1_tarski(k4_tarski(B_750,C_749))
      | ~ r2_hidden(k4_tarski(B_750,C_749),k1_wellord2(k1_tarski(C_749)))
      | ~ r2_hidden(C_749,k1_tarski(B_750)) ) ),
    inference(resolution,[status(thm)],[c_9608,c_177])).

tff(c_9942,plain,(
    ! [D_82,C_81] :
      ( k1_wellord2(k1_tarski(D_82)) = k1_tarski(k4_tarski(C_81,D_82))
      | ~ r2_hidden(D_82,k1_tarski(C_81))
      | ~ r1_tarski(C_81,D_82)
      | ~ r2_hidden(D_82,k1_tarski(D_82))
      | ~ r2_hidden(C_81,k1_tarski(D_82)) ) ),
    inference(resolution,[status(thm)],[c_104,c_9916])).

tff(c_9947,plain,(
    ! [D_751,C_752] :
      ( k1_wellord2(k1_tarski(D_751)) = k1_tarski(k4_tarski(C_752,D_751))
      | ~ r2_hidden(D_751,k1_tarski(C_752))
      | ~ r1_tarski(C_752,D_751)
      | ~ r2_hidden(C_752,k1_tarski(D_751)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_9942])).

tff(c_10027,plain,(
    ! [A_10] :
      ( k1_wellord2(k1_tarski(A_10)) = k1_tarski(k4_tarski(A_10,A_10))
      | ~ r1_tarski(A_10,A_10)
      | ~ r2_hidden(A_10,k1_tarski(A_10)) ) ),
    inference(resolution,[status(thm)],[c_153,c_9947])).

tff(c_10057,plain,(
    ! [A_10] : k1_wellord2(k1_tarski(A_10)) = k1_tarski(k4_tarski(A_10,A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_6,c_10027])).

tff(c_100,plain,(
    k1_wellord2(k1_tarski('#skF_13')) != k1_tarski(k4_tarski('#skF_13','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10057,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.75/3.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.28  
% 9.75/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > #skF_11 > #skF_6 > #skF_4 > #skF_8 > #skF_12 > #skF_2 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_1 > #skF_9
% 9.75/3.28  
% 9.75/3.28  %Foreground sorts:
% 9.75/3.28  
% 9.75/3.28  
% 9.75/3.28  %Background operators:
% 9.75/3.28  
% 9.75/3.28  
% 9.75/3.28  %Foreground operators:
% 9.75/3.28  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 9.75/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.75/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.75/3.28  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.75/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.75/3.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.75/3.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 9.75/3.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.75/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.75/3.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.75/3.28  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 9.75/3.28  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 9.75/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.75/3.28  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 9.75/3.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.75/3.28  tff('#skF_13', type, '#skF_13': $i).
% 9.75/3.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.75/3.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.75/3.28  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 9.75/3.28  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 9.75/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.75/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.75/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.75/3.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.75/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.75/3.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.75/3.28  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.75/3.28  
% 9.75/3.30  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.75/3.30  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.75/3.30  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.75/3.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.75/3.30  tff(f_107, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 9.75/3.30  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 9.75/3.30  tff(f_72, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 9.75/3.30  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 9.75/3.30  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 9.75/3.30  tff(f_64, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 9.75/3.30  tff(f_68, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.75/3.30  tff(f_110, negated_conjecture, ~(![A]: (k1_wellord2(k1_tarski(A)) = k1_tarski(k4_tarski(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_wellord2)).
% 9.75/3.30  tff(c_32, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.75/3.30  tff(c_131, plain, (![A_97, B_98]: (k1_enumset1(A_97, A_97, B_98)=k2_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.75/3.30  tff(c_10, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.75/3.30  tff(c_150, plain, (![B_101, A_102]: (r2_hidden(B_101, k2_tarski(A_102, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_10])).
% 9.75/3.30  tff(c_153, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_150])).
% 9.75/3.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.75/3.30  tff(c_98, plain, (![A_83]: (v1_relat_1(k1_wellord2(A_83)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.75/3.30  tff(c_94, plain, (![C_81, D_82, A_75]: (r2_hidden(k4_tarski(C_81, D_82), k1_wellord2(A_75)) | ~r1_tarski(C_81, D_82) | ~r2_hidden(D_82, A_75) | ~r2_hidden(C_81, A_75) | ~v1_relat_1(k1_wellord2(A_75)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.75/3.30  tff(c_104, plain, (![C_81, D_82, A_75]: (r2_hidden(k4_tarski(C_81, D_82), k1_wellord2(A_75)) | ~r1_tarski(C_81, D_82) | ~r2_hidden(D_82, A_75) | ~r2_hidden(C_81, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94])).
% 9.75/3.30  tff(c_324, plain, (![A_134, B_135, C_136]: (k2_zfmisc_1(k2_tarski(A_134, B_135), k1_tarski(C_136))=k2_tarski(k4_tarski(A_134, C_136), k4_tarski(B_135, C_136)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.75/3.30  tff(c_346, plain, (![B_135, C_136]: (k2_zfmisc_1(k2_tarski(B_135, B_135), k1_tarski(C_136))=k1_tarski(k4_tarski(B_135, C_136)))), inference(superposition, [status(thm), theory('equality')], [c_324, c_32])).
% 9.75/3.30  tff(c_365, plain, (![B_135, C_136]: (k2_zfmisc_1(k1_tarski(B_135), k1_tarski(C_136))=k1_tarski(k4_tarski(B_135, C_136)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_346])).
% 9.75/3.30  tff(c_92, plain, (![A_75]: (k3_relat_1(k1_wellord2(A_75))=A_75 | ~v1_relat_1(k1_wellord2(A_75)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.75/3.30  tff(c_106, plain, (![A_75]: (k3_relat_1(k1_wellord2(A_75))=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92])).
% 9.75/3.30  tff(c_652, plain, (![A_170, B_171]: (r2_hidden(k4_tarski('#skF_9'(A_170, B_171), '#skF_10'(A_170, B_171)), A_170) | r1_tarski(A_170, B_171) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.75/3.30  tff(c_76, plain, (![B_73, C_74, A_72]: (r2_hidden(B_73, k3_relat_1(C_74)) | ~r2_hidden(k4_tarski(A_72, B_73), C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.75/3.30  tff(c_712, plain, (![A_176, B_177]: (r2_hidden('#skF_10'(A_176, B_177), k3_relat_1(A_176)) | r1_tarski(A_176, B_177) | ~v1_relat_1(A_176))), inference(resolution, [status(thm)], [c_652, c_76])).
% 9.75/3.30  tff(c_715, plain, (![A_75, B_177]: (r2_hidden('#skF_10'(k1_wellord2(A_75), B_177), A_75) | r1_tarski(k1_wellord2(A_75), B_177) | ~v1_relat_1(k1_wellord2(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_712])).
% 9.75/3.30  tff(c_717, plain, (![A_75, B_177]: (r2_hidden('#skF_10'(k1_wellord2(A_75), B_177), A_75) | r1_tarski(k1_wellord2(A_75), B_177))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_715])).
% 9.75/3.30  tff(c_38, plain, (![E_48, F_49, A_16, B_17]: (r2_hidden(k4_tarski(E_48, F_49), k2_zfmisc_1(A_16, B_17)) | ~r2_hidden(F_49, B_17) | ~r2_hidden(E_48, A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.75/3.30  tff(c_78, plain, (![A_72, C_74, B_73]: (r2_hidden(A_72, k3_relat_1(C_74)) | ~r2_hidden(k4_tarski(A_72, B_73), C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.75/3.30  tff(c_686, plain, (![A_172, B_173]: (r2_hidden('#skF_9'(A_172, B_173), k3_relat_1(A_172)) | r1_tarski(A_172, B_173) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_652, c_78])).
% 9.75/3.30  tff(c_689, plain, (![A_75, B_173]: (r2_hidden('#skF_9'(k1_wellord2(A_75), B_173), A_75) | r1_tarski(k1_wellord2(A_75), B_173) | ~v1_relat_1(k1_wellord2(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_686])).
% 9.75/3.30  tff(c_691, plain, (![A_75, B_173]: (r2_hidden('#skF_9'(k1_wellord2(A_75), B_173), A_75) | r1_tarski(k1_wellord2(A_75), B_173))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_689])).
% 9.75/3.30  tff(c_568, plain, (![E_158, F_159, A_160, B_161]: (r2_hidden(k4_tarski(E_158, F_159), k2_zfmisc_1(A_160, B_161)) | ~r2_hidden(F_159, B_161) | ~r2_hidden(E_158, A_160))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.75/3.30  tff(c_1793, plain, (![E_301, F_302, B_303, C_304]: (r2_hidden(k4_tarski(E_301, F_302), k1_tarski(k4_tarski(B_303, C_304))) | ~r2_hidden(F_302, k1_tarski(C_304)) | ~r2_hidden(E_301, k1_tarski(B_303)))), inference(superposition, [status(thm), theory('equality')], [c_365, c_568])).
% 9.75/3.30  tff(c_34, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.75/3.30  tff(c_267, plain, (![E_121, C_122, B_123, A_124]: (E_121=C_122 | E_121=B_123 | E_121=A_124 | ~r2_hidden(E_121, k1_enumset1(A_124, B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.75/3.30  tff(c_286, plain, (![E_125, B_126, A_127]: (E_125=B_126 | E_125=A_127 | E_125=A_127 | ~r2_hidden(E_125, k2_tarski(A_127, B_126)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_267])).
% 9.75/3.30  tff(c_295, plain, (![E_125, A_10]: (E_125=A_10 | E_125=A_10 | E_125=A_10 | ~r2_hidden(E_125, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_286])).
% 9.75/3.30  tff(c_1823, plain, (![E_305, F_306, B_307, C_308]: (k4_tarski(E_305, F_306)=k4_tarski(B_307, C_308) | ~r2_hidden(F_306, k1_tarski(C_308)) | ~r2_hidden(E_305, k1_tarski(B_307)))), inference(resolution, [status(thm)], [c_1793, c_295])).
% 9.75/3.30  tff(c_1870, plain, (![E_309, A_310, B_311]: (k4_tarski(E_309, A_310)=k4_tarski(B_311, A_310) | ~r2_hidden(E_309, k1_tarski(B_311)))), inference(resolution, [status(thm)], [c_153, c_1823])).
% 9.75/3.30  tff(c_2084, plain, (![B_319, B_320, A_321]: (k4_tarski('#skF_9'(k1_wellord2(k1_tarski(B_319)), B_320), A_321)=k4_tarski(B_319, A_321) | r1_tarski(k1_wellord2(k1_tarski(B_319)), B_320))), inference(resolution, [status(thm)], [c_691, c_1870])).
% 9.75/3.30  tff(c_72, plain, (![A_55, B_65]: (~r2_hidden(k4_tarski('#skF_9'(A_55, B_65), '#skF_10'(A_55, B_65)), B_65) | r1_tarski(A_55, B_65) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.75/3.30  tff(c_2179, plain, (![B_319, B_320]: (~r2_hidden(k4_tarski(B_319, '#skF_10'(k1_wellord2(k1_tarski(B_319)), B_320)), B_320) | r1_tarski(k1_wellord2(k1_tarski(B_319)), B_320) | ~v1_relat_1(k1_wellord2(k1_tarski(B_319))) | r1_tarski(k1_wellord2(k1_tarski(B_319)), B_320))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_72])).
% 9.75/3.30  tff(c_2228, plain, (![B_322, B_323]: (~r2_hidden(k4_tarski(B_322, '#skF_10'(k1_wellord2(k1_tarski(B_322)), B_323)), B_323) | r1_tarski(k1_wellord2(k1_tarski(B_322)), B_323))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2179])).
% 9.75/3.30  tff(c_9451, plain, (![E_711, A_712, B_713]: (r1_tarski(k1_wellord2(k1_tarski(E_711)), k2_zfmisc_1(A_712, B_713)) | ~r2_hidden('#skF_10'(k1_wellord2(k1_tarski(E_711)), k2_zfmisc_1(A_712, B_713)), B_713) | ~r2_hidden(E_711, A_712))), inference(resolution, [status(thm)], [c_38, c_2228])).
% 9.75/3.30  tff(c_9586, plain, (![E_714, A_715]: (~r2_hidden(E_714, A_715) | r1_tarski(k1_wellord2(k1_tarski(E_714)), k2_zfmisc_1(A_715, k1_tarski(E_714))))), inference(resolution, [status(thm)], [c_717, c_9451])).
% 9.75/3.30  tff(c_9608, plain, (![C_716, B_717]: (~r2_hidden(C_716, k1_tarski(B_717)) | r1_tarski(k1_wellord2(k1_tarski(C_716)), k1_tarski(k4_tarski(B_717, C_716))))), inference(superposition, [status(thm), theory('equality')], [c_365, c_9586])).
% 9.75/3.30  tff(c_64, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.75/3.30  tff(c_172, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.75/3.30  tff(c_177, plain, (![A_50, B_51]: (k1_tarski(A_50)=B_51 | ~r1_tarski(B_51, k1_tarski(A_50)) | ~r2_hidden(A_50, B_51))), inference(resolution, [status(thm)], [c_64, c_172])).
% 9.75/3.30  tff(c_9916, plain, (![C_749, B_750]: (k1_wellord2(k1_tarski(C_749))=k1_tarski(k4_tarski(B_750, C_749)) | ~r2_hidden(k4_tarski(B_750, C_749), k1_wellord2(k1_tarski(C_749))) | ~r2_hidden(C_749, k1_tarski(B_750)))), inference(resolution, [status(thm)], [c_9608, c_177])).
% 9.75/3.30  tff(c_9942, plain, (![D_82, C_81]: (k1_wellord2(k1_tarski(D_82))=k1_tarski(k4_tarski(C_81, D_82)) | ~r2_hidden(D_82, k1_tarski(C_81)) | ~r1_tarski(C_81, D_82) | ~r2_hidden(D_82, k1_tarski(D_82)) | ~r2_hidden(C_81, k1_tarski(D_82)))), inference(resolution, [status(thm)], [c_104, c_9916])).
% 9.75/3.30  tff(c_9947, plain, (![D_751, C_752]: (k1_wellord2(k1_tarski(D_751))=k1_tarski(k4_tarski(C_752, D_751)) | ~r2_hidden(D_751, k1_tarski(C_752)) | ~r1_tarski(C_752, D_751) | ~r2_hidden(C_752, k1_tarski(D_751)))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_9942])).
% 9.75/3.30  tff(c_10027, plain, (![A_10]: (k1_wellord2(k1_tarski(A_10))=k1_tarski(k4_tarski(A_10, A_10)) | ~r1_tarski(A_10, A_10) | ~r2_hidden(A_10, k1_tarski(A_10)))), inference(resolution, [status(thm)], [c_153, c_9947])).
% 9.75/3.30  tff(c_10057, plain, (![A_10]: (k1_wellord2(k1_tarski(A_10))=k1_tarski(k4_tarski(A_10, A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_6, c_10027])).
% 9.75/3.30  tff(c_100, plain, (k1_wellord2(k1_tarski('#skF_13'))!=k1_tarski(k4_tarski('#skF_13', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.75/3.30  tff(c_10172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10057, c_100])).
% 9.75/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.30  
% 9.75/3.30  Inference rules
% 9.75/3.30  ----------------------
% 9.75/3.30  #Ref     : 0
% 9.75/3.30  #Sup     : 2675
% 9.75/3.30  #Fact    : 0
% 9.75/3.30  #Define  : 0
% 9.75/3.30  #Split   : 0
% 9.75/3.30  #Chain   : 0
% 9.75/3.30  #Close   : 0
% 9.75/3.30  
% 9.75/3.30  Ordering : KBO
% 9.75/3.30  
% 9.75/3.30  Simplification rules
% 9.75/3.30  ----------------------
% 9.75/3.30  #Subsume      : 353
% 9.75/3.30  #Demod        : 581
% 9.75/3.30  #Tautology    : 189
% 9.75/3.30  #SimpNegUnit  : 0
% 9.75/3.30  #BackRed      : 1
% 9.75/3.30  
% 9.75/3.30  #Partial instantiations: 0
% 9.75/3.30  #Strategies tried      : 1
% 9.75/3.30  
% 9.75/3.30  Timing (in seconds)
% 9.75/3.30  ----------------------
% 9.75/3.31  Preprocessing        : 0.36
% 9.75/3.31  Parsing              : 0.17
% 9.75/3.31  CNF conversion       : 0.03
% 9.75/3.31  Main loop            : 2.19
% 9.75/3.31  Inferencing          : 0.61
% 9.75/3.31  Reduction            : 0.74
% 9.75/3.31  Demodulation         : 0.59
% 9.75/3.31  BG Simplification    : 0.10
% 9.75/3.31  Subsumption          : 0.61
% 9.75/3.31  Abstraction          : 0.12
% 9.75/3.31  MUC search           : 0.00
% 9.75/3.31  Cooper               : 0.00
% 9.75/3.31  Total                : 2.59
% 9.75/3.31  Index Insertion      : 0.00
% 9.75/3.31  Index Deletion       : 0.00
% 9.75/3.31  Index Matching       : 0.00
% 9.75/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
