%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:07 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 283 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 ( 631 expanded)
%              Number of equality atoms :   11 (  71 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_32,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(k1_tarski(A_52),B_53) = B_53
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_52,c_8])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(k1_tarski(A_63),C_64)
      | ~ r1_tarski(B_65,C_64)
      | ~ r2_hidden(A_63,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_134,plain,(
    ! [A_66] :
      ( r1_tarski(k1_tarski(A_66),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_66,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | ~ r1_tarski(k1_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [A_66] :
      ( r2_hidden(A_66,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_66,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_134,c_12])).

tff(c_34,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_35,plain,(
    ! [B_29,A_30] :
      ( ~ r2_hidden(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_35])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ r2_hidden(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_73,plain,
    ( m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_77,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_73])).

tff(c_250,plain,(
    ! [A_90,B_91,C_92] :
      ( k4_tarski('#skF_2'(A_90,B_91,C_92),'#skF_3'(A_90,B_91,C_92)) = A_90
      | ~ r2_hidden(A_90,k2_zfmisc_1(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [B_18,D_20,A_17,C_19] :
      ( r2_hidden(B_18,D_20)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_500,plain,(
    ! [A_134,C_133,C_130,B_131,D_132] :
      ( r2_hidden('#skF_3'(A_134,B_131,C_133),D_132)
      | ~ r2_hidden(A_134,k2_zfmisc_1(C_130,D_132))
      | ~ r2_hidden(A_134,k2_zfmisc_1(B_131,C_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_18])).

tff(c_522,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden('#skF_3'(A_135,B_136,C_137),'#skF_5')
      | ~ r2_hidden(A_135,k2_zfmisc_1(B_136,C_137))
      | ~ r2_hidden(A_135,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_500])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_533,plain,(
    ! [A_135,B_136,C_137] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_135,k2_zfmisc_1(B_136,C_137))
      | ~ r2_hidden(A_135,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_522,c_2])).

tff(c_534,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_146,plain,(
    ! [A_67] :
      ( r2_hidden(A_67,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_67,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_134,c_12])).

tff(c_190,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_75,B_74),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_146,c_18])).

tff(c_193,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_75,B_74),'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_190])).

tff(c_196,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_75,B_74),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_193])).

tff(c_541,plain,(
    ! [A_141,B_142,C_143] :
      ( r2_hidden('#skF_3'(A_141,B_142,C_143),'#skF_5')
      | ~ m1_subset_1(A_141,'#skF_6')
      | ~ r2_hidden(A_141,k2_zfmisc_1(B_142,C_143)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_196])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ r2_hidden(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_546,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_subset_1('#skF_3'(A_141,B_142,C_143),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_141,'#skF_6')
      | ~ r2_hidden(A_141,k2_zfmisc_1(B_142,C_143)) ) ),
    inference(resolution,[status(thm)],[c_541,c_22])).

tff(c_585,plain,(
    ! [A_151,B_152,C_153] :
      ( m1_subset_1('#skF_3'(A_151,B_152,C_153),'#skF_5')
      | ~ m1_subset_1(A_151,'#skF_6')
      | ~ r2_hidden(A_151,k2_zfmisc_1(B_152,C_153)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_546])).

tff(c_610,plain,(
    ! [A_66] :
      ( m1_subset_1('#skF_3'(A_66,'#skF_4','#skF_5'),'#skF_5')
      | ~ m1_subset_1(A_66,'#skF_6')
      | ~ r2_hidden(A_66,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_585])).

tff(c_20,plain,(
    ! [A_17,C_19,B_18,D_20] :
      ( r2_hidden(A_17,C_19)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_404,plain,(
    ! [C_115,A_119,B_116,D_117,C_118] :
      ( r2_hidden('#skF_2'(A_119,B_116,C_118),C_115)
      | ~ r2_hidden(A_119,k2_zfmisc_1(C_115,D_117))
      | ~ r2_hidden(A_119,k2_zfmisc_1(B_116,C_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_20])).

tff(c_487,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_2'(A_127,B_128,C_129),'#skF_4')
      | ~ r2_hidden(A_127,k2_zfmisc_1(B_128,C_129))
      | ~ r2_hidden(A_127,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_404])).

tff(c_498,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_127,k2_zfmisc_1(B_128,C_129))
      | ~ r2_hidden(A_127,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_487,c_2])).

tff(c_499,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_183,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_72,B_73),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_146,c_20])).

tff(c_186,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,'#skF_4')
      | ~ m1_subset_1(k4_tarski(A_72,B_73),'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_183])).

tff(c_189,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,'#skF_4')
      | ~ m1_subset_1(k4_tarski(A_72,B_73),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_186])).

tff(c_555,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_2'(A_144,B_145,C_146),'#skF_4')
      | ~ m1_subset_1(A_144,'#skF_6')
      | ~ r2_hidden(A_144,k2_zfmisc_1(B_145,C_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_189])).

tff(c_560,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1('#skF_2'(A_144,B_145,C_146),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_144,'#skF_6')
      | ~ r2_hidden(A_144,k2_zfmisc_1(B_145,C_146)) ) ),
    inference(resolution,[status(thm)],[c_555,c_22])).

tff(c_618,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_subset_1('#skF_2'(A_155,B_156,C_157),'#skF_4')
      | ~ m1_subset_1(A_155,'#skF_6')
      | ~ r2_hidden(A_155,k2_zfmisc_1(B_156,C_157)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_560])).

tff(c_654,plain,(
    ! [A_162] :
      ( m1_subset_1('#skF_2'(A_162,'#skF_4','#skF_5'),'#skF_4')
      | ~ m1_subset_1(A_162,'#skF_6')
      | ~ r2_hidden(A_162,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_618])).

tff(c_30,plain,(
    ! [E_26,F_28] :
      ( k4_tarski(E_26,F_28) != '#skF_7'
      | ~ m1_subset_1(F_28,'#skF_5')
      | ~ m1_subset_1(E_26,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_303,plain,(
    ! [A_98,B_99,C_100] :
      ( A_98 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_98,B_99,C_100),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_98,B_99,C_100),'#skF_4')
      | ~ r2_hidden(A_98,k2_zfmisc_1(B_99,C_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_30])).

tff(c_324,plain,(
    ! [A_66] :
      ( A_66 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_66,'#skF_4','#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_66,'#skF_4','#skF_5'),'#skF_4')
      | ~ r2_hidden(A_66,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_303])).

tff(c_675,plain,(
    ! [A_163] :
      ( A_163 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_163,'#skF_4','#skF_5'),'#skF_5')
      | ~ m1_subset_1(A_163,'#skF_6')
      | ~ r2_hidden(A_163,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_654,c_324])).

tff(c_685,plain,(
    ! [A_164] :
      ( A_164 != '#skF_7'
      | ~ m1_subset_1(A_164,'#skF_6')
      | ~ r2_hidden(A_164,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_610,c_675])).

tff(c_700,plain,(
    ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_685])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_700])).

tff(c_714,plain,(
    ! [A_165,B_166,C_167] :
      ( ~ r2_hidden(A_165,k2_zfmisc_1(B_166,C_167))
      | ~ r2_hidden(A_165,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_739,plain,(
    ! [A_66] : ~ r2_hidden(A_66,'#skF_6') ),
    inference(resolution,[status(thm)],[c_145,c_714])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_34])).

tff(c_762,plain,(
    ! [A_172,B_173,C_174] :
      ( ~ r2_hidden(A_172,k2_zfmisc_1(B_173,C_174))
      | ~ r2_hidden(A_172,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_787,plain,(
    ! [A_66] : ~ r2_hidden(A_66,'#skF_6') ),
    inference(resolution,[status(thm)],[c_145,c_762])).

tff(c_798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.21/1.51  
% 3.21/1.51  %Foreground sorts:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Background operators:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Foreground operators:
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.21/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.21/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.21/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.51  
% 3.21/1.53  tff(f_84, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 3.21/1.53  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.21/1.53  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.21/1.53  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.21/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.21/1.53  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.21/1.53  tff(f_46, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.21/1.53  tff(f_56, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.21/1.53  tff(c_32, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.53  tff(c_52, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.53  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.53  tff(c_104, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)=B_53 | ~r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_52, c_8])).
% 3.21/1.53  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.53  tff(c_127, plain, (![A_63, C_64, B_65]: (r1_tarski(k1_tarski(A_63), C_64) | ~r1_tarski(B_65, C_64) | ~r2_hidden(A_63, B_65))), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 3.21/1.53  tff(c_134, plain, (![A_66]: (r1_tarski(k1_tarski(A_66), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_127])).
% 3.21/1.53  tff(c_12, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | ~r1_tarski(k1_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.53  tff(c_145, plain, (![A_66]: (r2_hidden(A_66, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_134, c_12])).
% 3.21/1.53  tff(c_34, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.53  tff(c_35, plain, (![B_29, A_30]: (~r2_hidden(B_29, A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.53  tff(c_39, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_34, c_35])).
% 3.21/1.53  tff(c_67, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~r2_hidden(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.53  tff(c_73, plain, (m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_34, c_67])).
% 3.21/1.53  tff(c_77, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_39, c_73])).
% 3.21/1.53  tff(c_250, plain, (![A_90, B_91, C_92]: (k4_tarski('#skF_2'(A_90, B_91, C_92), '#skF_3'(A_90, B_91, C_92))=A_90 | ~r2_hidden(A_90, k2_zfmisc_1(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.53  tff(c_18, plain, (![B_18, D_20, A_17, C_19]: (r2_hidden(B_18, D_20) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.53  tff(c_500, plain, (![A_134, C_133, C_130, B_131, D_132]: (r2_hidden('#skF_3'(A_134, B_131, C_133), D_132) | ~r2_hidden(A_134, k2_zfmisc_1(C_130, D_132)) | ~r2_hidden(A_134, k2_zfmisc_1(B_131, C_133)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_18])).
% 3.21/1.53  tff(c_522, plain, (![A_135, B_136, C_137]: (r2_hidden('#skF_3'(A_135, B_136, C_137), '#skF_5') | ~r2_hidden(A_135, k2_zfmisc_1(B_136, C_137)) | ~r2_hidden(A_135, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_500])).
% 3.21/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.53  tff(c_533, plain, (![A_135, B_136, C_137]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_135, k2_zfmisc_1(B_136, C_137)) | ~r2_hidden(A_135, '#skF_6'))), inference(resolution, [status(thm)], [c_522, c_2])).
% 3.21/1.53  tff(c_534, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_533])).
% 3.21/1.53  tff(c_24, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.53  tff(c_146, plain, (![A_67]: (r2_hidden(A_67, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_67, '#skF_6'))), inference(resolution, [status(thm)], [c_134, c_12])).
% 3.21/1.53  tff(c_190, plain, (![B_74, A_75]: (r2_hidden(B_74, '#skF_5') | ~r2_hidden(k4_tarski(A_75, B_74), '#skF_6'))), inference(resolution, [status(thm)], [c_146, c_18])).
% 3.21/1.53  tff(c_193, plain, (![B_74, A_75]: (r2_hidden(B_74, '#skF_5') | ~m1_subset_1(k4_tarski(A_75, B_74), '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_190])).
% 3.21/1.53  tff(c_196, plain, (![B_74, A_75]: (r2_hidden(B_74, '#skF_5') | ~m1_subset_1(k4_tarski(A_75, B_74), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_39, c_193])).
% 3.21/1.53  tff(c_541, plain, (![A_141, B_142, C_143]: (r2_hidden('#skF_3'(A_141, B_142, C_143), '#skF_5') | ~m1_subset_1(A_141, '#skF_6') | ~r2_hidden(A_141, k2_zfmisc_1(B_142, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_196])).
% 3.21/1.53  tff(c_22, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~r2_hidden(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.53  tff(c_546, plain, (![A_141, B_142, C_143]: (m1_subset_1('#skF_3'(A_141, B_142, C_143), '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(A_141, '#skF_6') | ~r2_hidden(A_141, k2_zfmisc_1(B_142, C_143)))), inference(resolution, [status(thm)], [c_541, c_22])).
% 3.21/1.53  tff(c_585, plain, (![A_151, B_152, C_153]: (m1_subset_1('#skF_3'(A_151, B_152, C_153), '#skF_5') | ~m1_subset_1(A_151, '#skF_6') | ~r2_hidden(A_151, k2_zfmisc_1(B_152, C_153)))), inference(negUnitSimplification, [status(thm)], [c_534, c_546])).
% 3.21/1.53  tff(c_610, plain, (![A_66]: (m1_subset_1('#skF_3'(A_66, '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1(A_66, '#skF_6') | ~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_585])).
% 3.21/1.53  tff(c_20, plain, (![A_17, C_19, B_18, D_20]: (r2_hidden(A_17, C_19) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.53  tff(c_404, plain, (![C_115, A_119, B_116, D_117, C_118]: (r2_hidden('#skF_2'(A_119, B_116, C_118), C_115) | ~r2_hidden(A_119, k2_zfmisc_1(C_115, D_117)) | ~r2_hidden(A_119, k2_zfmisc_1(B_116, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_20])).
% 3.21/1.53  tff(c_487, plain, (![A_127, B_128, C_129]: (r2_hidden('#skF_2'(A_127, B_128, C_129), '#skF_4') | ~r2_hidden(A_127, k2_zfmisc_1(B_128, C_129)) | ~r2_hidden(A_127, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_404])).
% 3.21/1.53  tff(c_498, plain, (![A_127, B_128, C_129]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_127, k2_zfmisc_1(B_128, C_129)) | ~r2_hidden(A_127, '#skF_6'))), inference(resolution, [status(thm)], [c_487, c_2])).
% 3.21/1.53  tff(c_499, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_498])).
% 3.21/1.53  tff(c_183, plain, (![A_72, B_73]: (r2_hidden(A_72, '#skF_4') | ~r2_hidden(k4_tarski(A_72, B_73), '#skF_6'))), inference(resolution, [status(thm)], [c_146, c_20])).
% 3.21/1.53  tff(c_186, plain, (![A_72, B_73]: (r2_hidden(A_72, '#skF_4') | ~m1_subset_1(k4_tarski(A_72, B_73), '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_183])).
% 3.21/1.53  tff(c_189, plain, (![A_72, B_73]: (r2_hidden(A_72, '#skF_4') | ~m1_subset_1(k4_tarski(A_72, B_73), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_39, c_186])).
% 3.21/1.53  tff(c_555, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_2'(A_144, B_145, C_146), '#skF_4') | ~m1_subset_1(A_144, '#skF_6') | ~r2_hidden(A_144, k2_zfmisc_1(B_145, C_146)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_189])).
% 3.21/1.53  tff(c_560, plain, (![A_144, B_145, C_146]: (m1_subset_1('#skF_2'(A_144, B_145, C_146), '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_144, '#skF_6') | ~r2_hidden(A_144, k2_zfmisc_1(B_145, C_146)))), inference(resolution, [status(thm)], [c_555, c_22])).
% 3.21/1.53  tff(c_618, plain, (![A_155, B_156, C_157]: (m1_subset_1('#skF_2'(A_155, B_156, C_157), '#skF_4') | ~m1_subset_1(A_155, '#skF_6') | ~r2_hidden(A_155, k2_zfmisc_1(B_156, C_157)))), inference(negUnitSimplification, [status(thm)], [c_499, c_560])).
% 3.21/1.53  tff(c_654, plain, (![A_162]: (m1_subset_1('#skF_2'(A_162, '#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1(A_162, '#skF_6') | ~r2_hidden(A_162, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_618])).
% 3.21/1.53  tff(c_30, plain, (![E_26, F_28]: (k4_tarski(E_26, F_28)!='#skF_7' | ~m1_subset_1(F_28, '#skF_5') | ~m1_subset_1(E_26, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.53  tff(c_303, plain, (![A_98, B_99, C_100]: (A_98!='#skF_7' | ~m1_subset_1('#skF_3'(A_98, B_99, C_100), '#skF_5') | ~m1_subset_1('#skF_2'(A_98, B_99, C_100), '#skF_4') | ~r2_hidden(A_98, k2_zfmisc_1(B_99, C_100)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_30])).
% 3.21/1.53  tff(c_324, plain, (![A_66]: (A_66!='#skF_7' | ~m1_subset_1('#skF_3'(A_66, '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_2'(A_66, '#skF_4', '#skF_5'), '#skF_4') | ~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_303])).
% 3.21/1.53  tff(c_675, plain, (![A_163]: (A_163!='#skF_7' | ~m1_subset_1('#skF_3'(A_163, '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1(A_163, '#skF_6') | ~r2_hidden(A_163, '#skF_6'))), inference(resolution, [status(thm)], [c_654, c_324])).
% 3.21/1.53  tff(c_685, plain, (![A_164]: (A_164!='#skF_7' | ~m1_subset_1(A_164, '#skF_6') | ~r2_hidden(A_164, '#skF_6'))), inference(resolution, [status(thm)], [c_610, c_675])).
% 3.21/1.53  tff(c_700, plain, (~m1_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_685])).
% 3.21/1.53  tff(c_711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_700])).
% 3.21/1.53  tff(c_714, plain, (![A_165, B_166, C_167]: (~r2_hidden(A_165, k2_zfmisc_1(B_166, C_167)) | ~r2_hidden(A_165, '#skF_6'))), inference(splitRight, [status(thm)], [c_533])).
% 3.21/1.53  tff(c_739, plain, (![A_66]: (~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_714])).
% 3.21/1.53  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_739, c_34])).
% 3.21/1.53  tff(c_762, plain, (![A_172, B_173, C_174]: (~r2_hidden(A_172, k2_zfmisc_1(B_173, C_174)) | ~r2_hidden(A_172, '#skF_6'))), inference(splitRight, [status(thm)], [c_498])).
% 3.21/1.53  tff(c_787, plain, (![A_66]: (~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_762])).
% 3.21/1.53  tff(c_798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_34])).
% 3.21/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.53  
% 3.21/1.53  Inference rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Ref     : 0
% 3.21/1.53  #Sup     : 169
% 3.21/1.53  #Fact    : 0
% 3.21/1.53  #Define  : 0
% 3.21/1.53  #Split   : 4
% 3.21/1.53  #Chain   : 0
% 3.21/1.53  #Close   : 0
% 3.21/1.53  
% 3.21/1.53  Ordering : KBO
% 3.21/1.53  
% 3.21/1.53  Simplification rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Subsume      : 51
% 3.21/1.53  #Demod        : 2
% 3.21/1.53  #Tautology    : 30
% 3.21/1.53  #SimpNegUnit  : 14
% 3.21/1.53  #BackRed      : 2
% 3.21/1.53  
% 3.21/1.53  #Partial instantiations: 0
% 3.21/1.53  #Strategies tried      : 1
% 3.21/1.53  
% 3.21/1.53  Timing (in seconds)
% 3.21/1.53  ----------------------
% 3.21/1.53  Preprocessing        : 0.31
% 3.21/1.53  Parsing              : 0.17
% 3.21/1.53  CNF conversion       : 0.03
% 3.21/1.53  Main loop            : 0.42
% 3.21/1.53  Inferencing          : 0.17
% 3.21/1.53  Reduction            : 0.10
% 3.21/1.53  Demodulation         : 0.06
% 3.21/1.53  BG Simplification    : 0.02
% 3.21/1.53  Subsumption          : 0.10
% 3.21/1.53  Abstraction          : 0.02
% 3.21/1.53  MUC search           : 0.00
% 3.21/1.53  Cooper               : 0.00
% 3.21/1.53  Total                : 0.77
% 3.21/1.53  Index Insertion      : 0.00
% 3.21/1.53  Index Deletion       : 0.00
% 3.21/1.53  Index Matching       : 0.00
% 3.21/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
