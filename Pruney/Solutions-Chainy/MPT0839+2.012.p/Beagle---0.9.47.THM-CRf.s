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
% DateTime   : Thu Dec  3 10:08:23 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 203 expanded)
%              Number of leaves         :   38 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 406 expanded)
%              Number of equality atoms :   34 ( 108 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_48,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_77,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_86,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_30,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = k1_xboole_0
      | k2_relat_1(A_28) != k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_30])).

tff(c_96,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_91,plain,(
    ! [A_67] :
      ( k2_relat_1(A_67) = k1_xboole_0
      | k1_relat_1(A_67) != k1_xboole_0
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_91])).

tff(c_97,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_95])).

tff(c_151,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_160,plain,(
    v4_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_151])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_294,plain,(
    ! [C_119,A_120] :
      ( r2_hidden(k4_tarski(C_119,'#skF_4'(A_120,k1_relat_1(A_120),C_119)),A_120)
      | ~ r2_hidden(C_119,k1_relat_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [A_92,C_93,B_94] :
      ( m1_subset_1(A_92,C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    ! [A_92,B_3,A_2] :
      ( m1_subset_1(A_92,B_3)
      | ~ r2_hidden(A_92,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_198])).

tff(c_410,plain,(
    ! [C_149,A_150,B_151] :
      ( m1_subset_1(k4_tarski(C_149,'#skF_4'(A_150,k1_relat_1(A_150),C_149)),B_151)
      | ~ r1_tarski(A_150,B_151)
      | ~ r2_hidden(C_149,k1_relat_1(A_150)) ) ),
    inference(resolution,[status(thm)],[c_294,c_203])).

tff(c_247,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_256,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_247])).

tff(c_46,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ m1_subset_1(D_54,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_264,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_54,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_46])).

tff(c_310,plain,(
    ! [C_119] :
      ( ~ m1_subset_1(k4_tarski(C_119,'#skF_4'(k1_relat_1('#skF_7'),k1_relat_1(k1_relat_1('#skF_7')),C_119)),'#skF_6')
      | ~ r2_hidden(C_119,k1_relat_1(k1_relat_1('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_294,c_264])).

tff(c_445,plain,(
    ! [C_149] :
      ( ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
      | ~ r2_hidden(C_149,k1_relat_1(k1_relat_1('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_410,c_310])).

tff(c_455,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_458,plain,
    ( ~ v4_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_455])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_160,c_458])).

tff(c_464,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_482,plain,(
    ! [A_153,B_154] :
      ( r2_hidden(k4_tarski('#skF_1'(A_153,B_154),'#skF_2'(A_153,B_154)),A_153)
      | r2_hidden('#skF_3'(A_153,B_154),B_154)
      | k1_relat_1(A_153) = B_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_309,plain,(
    ! [C_119] :
      ( r2_hidden(k4_tarski(C_119,'#skF_4'(k1_xboole_0,k1_xboole_0,C_119)),k1_xboole_0)
      | ~ r2_hidden(C_119,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_294])).

tff(c_315,plain,(
    ! [C_121] :
      ( r2_hidden(k4_tarski(C_121,'#skF_4'(k1_xboole_0,k1_xboole_0,C_121)),k1_xboole_0)
      | ~ r2_hidden(C_121,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_309])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_323,plain,(
    ! [C_121] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_121,'#skF_4'(k1_xboole_0,k1_xboole_0,C_121)))
      | ~ r2_hidden(C_121,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_315,c_34])).

tff(c_331,plain,(
    ! [C_121] : ~ r2_hidden(C_121,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_323])).

tff(c_490,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_154),B_154)
      | k1_relat_1(k1_xboole_0) = B_154 ) ),
    inference(resolution,[status(thm)],[c_482,c_331])).

tff(c_526,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_156),B_156)
      | k1_xboole_0 = B_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_490])).

tff(c_607,plain,(
    ! [B_162,B_163] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_162),B_163)
      | ~ r1_tarski(B_162,B_163)
      | k1_xboole_0 = B_162 ) ),
    inference(resolution,[status(thm)],[c_526,c_203])).

tff(c_542,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_526,c_264])).

tff(c_554,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_542])).

tff(c_610,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_607,c_554])).

tff(c_640,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_610])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_640])).

tff(c_643,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_650,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_95])).

tff(c_775,plain,(
    ! [A_192,B_193,C_194] :
      ( k2_relset_1(A_192,B_193,C_194) = k2_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_782,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_775])).

tff(c_785,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_782])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:16:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.42  
% 2.89/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.89/1.43  
% 2.89/1.43  %Foreground sorts:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Background operators:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Foreground operators:
% 2.89/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.89/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.89/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.89/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.89/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.43  
% 2.89/1.44  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.89/1.44  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.89/1.44  tff(f_60, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.89/1.44  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.89/1.44  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.89/1.44  tff(f_51, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.89/1.44  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.44  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.89/1.44  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.89/1.44  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.89/1.44  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.89/1.44  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.89/1.44  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.89/1.44  tff(c_48, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.44  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.44  tff(c_77, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.44  tff(c_86, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_77])).
% 2.89/1.44  tff(c_30, plain, (![A_28]: (k1_relat_1(A_28)=k1_xboole_0 | k2_relat_1(A_28)!=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.44  tff(c_90, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_30])).
% 2.89/1.44  tff(c_96, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 2.89/1.44  tff(c_91, plain, (![A_67]: (k2_relat_1(A_67)=k1_xboole_0 | k1_relat_1(A_67)!=k1_xboole_0 | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.44  tff(c_95, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_91])).
% 2.89/1.44  tff(c_97, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_96, c_95])).
% 2.89/1.44  tff(c_151, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.44  tff(c_160, plain, (v4_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_151])).
% 2.89/1.44  tff(c_12, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.44  tff(c_294, plain, (![C_119, A_120]: (r2_hidden(k4_tarski(C_119, '#skF_4'(A_120, k1_relat_1(A_120), C_119)), A_120) | ~r2_hidden(C_119, k1_relat_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.44  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.44  tff(c_198, plain, (![A_92, C_93, B_94]: (m1_subset_1(A_92, C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.44  tff(c_203, plain, (![A_92, B_3, A_2]: (m1_subset_1(A_92, B_3) | ~r2_hidden(A_92, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_6, c_198])).
% 2.89/1.44  tff(c_410, plain, (![C_149, A_150, B_151]: (m1_subset_1(k4_tarski(C_149, '#skF_4'(A_150, k1_relat_1(A_150), C_149)), B_151) | ~r1_tarski(A_150, B_151) | ~r2_hidden(C_149, k1_relat_1(A_150)))), inference(resolution, [status(thm)], [c_294, c_203])).
% 2.89/1.44  tff(c_247, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.89/1.44  tff(c_256, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_247])).
% 2.89/1.44  tff(c_46, plain, (![D_54]: (~r2_hidden(D_54, k1_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_subset_1(D_54, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.89/1.44  tff(c_264, plain, (![D_54]: (~r2_hidden(D_54, k1_relat_1('#skF_7')) | ~m1_subset_1(D_54, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_46])).
% 2.89/1.44  tff(c_310, plain, (![C_119]: (~m1_subset_1(k4_tarski(C_119, '#skF_4'(k1_relat_1('#skF_7'), k1_relat_1(k1_relat_1('#skF_7')), C_119)), '#skF_6') | ~r2_hidden(C_119, k1_relat_1(k1_relat_1('#skF_7'))))), inference(resolution, [status(thm)], [c_294, c_264])).
% 2.89/1.44  tff(c_445, plain, (![C_149]: (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | ~r2_hidden(C_149, k1_relat_1(k1_relat_1('#skF_7'))))), inference(resolution, [status(thm)], [c_410, c_310])).
% 2.89/1.44  tff(c_455, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_445])).
% 2.89/1.44  tff(c_458, plain, (~v4_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_455])).
% 2.89/1.44  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_160, c_458])).
% 2.89/1.44  tff(c_464, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_445])).
% 2.89/1.44  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.44  tff(c_482, plain, (![A_153, B_154]: (r2_hidden(k4_tarski('#skF_1'(A_153, B_154), '#skF_2'(A_153, B_154)), A_153) | r2_hidden('#skF_3'(A_153, B_154), B_154) | k1_relat_1(A_153)=B_154)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.44  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.44  tff(c_309, plain, (![C_119]: (r2_hidden(k4_tarski(C_119, '#skF_4'(k1_xboole_0, k1_xboole_0, C_119)), k1_xboole_0) | ~r2_hidden(C_119, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_294])).
% 2.89/1.44  tff(c_315, plain, (![C_121]: (r2_hidden(k4_tarski(C_121, '#skF_4'(k1_xboole_0, k1_xboole_0, C_121)), k1_xboole_0) | ~r2_hidden(C_121, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_309])).
% 2.89/1.44  tff(c_34, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.44  tff(c_323, plain, (![C_121]: (~r1_tarski(k1_xboole_0, k4_tarski(C_121, '#skF_4'(k1_xboole_0, k1_xboole_0, C_121))) | ~r2_hidden(C_121, k1_xboole_0))), inference(resolution, [status(thm)], [c_315, c_34])).
% 2.89/1.44  tff(c_331, plain, (![C_121]: (~r2_hidden(C_121, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_323])).
% 2.89/1.44  tff(c_490, plain, (![B_154]: (r2_hidden('#skF_3'(k1_xboole_0, B_154), B_154) | k1_relat_1(k1_xboole_0)=B_154)), inference(resolution, [status(thm)], [c_482, c_331])).
% 2.89/1.44  tff(c_526, plain, (![B_156]: (r2_hidden('#skF_3'(k1_xboole_0, B_156), B_156) | k1_xboole_0=B_156)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_490])).
% 2.89/1.44  tff(c_607, plain, (![B_162, B_163]: (m1_subset_1('#skF_3'(k1_xboole_0, B_162), B_163) | ~r1_tarski(B_162, B_163) | k1_xboole_0=B_162)), inference(resolution, [status(thm)], [c_526, c_203])).
% 2.89/1.44  tff(c_542, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_526, c_264])).
% 2.89/1.44  tff(c_554, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_97, c_542])).
% 2.89/1.44  tff(c_610, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_607, c_554])).
% 2.89/1.44  tff(c_640, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_464, c_610])).
% 2.89/1.44  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_640])).
% 2.89/1.44  tff(c_643, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 2.89/1.44  tff(c_650, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_643, c_95])).
% 2.89/1.44  tff(c_775, plain, (![A_192, B_193, C_194]: (k2_relset_1(A_192, B_193, C_194)=k2_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.89/1.44  tff(c_782, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_775])).
% 2.89/1.44  tff(c_785, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_650, c_782])).
% 2.89/1.44  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_785])).
% 2.89/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  Inference rules
% 2.89/1.44  ----------------------
% 2.89/1.44  #Ref     : 0
% 2.89/1.44  #Sup     : 143
% 2.89/1.44  #Fact    : 0
% 2.89/1.44  #Define  : 0
% 2.89/1.44  #Split   : 3
% 2.89/1.44  #Chain   : 0
% 2.89/1.44  #Close   : 0
% 2.89/1.44  
% 2.89/1.44  Ordering : KBO
% 2.89/1.44  
% 2.89/1.44  Simplification rules
% 2.89/1.44  ----------------------
% 2.89/1.44  #Subsume      : 17
% 2.89/1.44  #Demod        : 88
% 2.89/1.44  #Tautology    : 52
% 2.89/1.44  #SimpNegUnit  : 5
% 2.89/1.44  #BackRed      : 4
% 2.89/1.44  
% 2.89/1.44  #Partial instantiations: 0
% 2.89/1.44  #Strategies tried      : 1
% 2.89/1.44  
% 2.89/1.44  Timing (in seconds)
% 2.89/1.44  ----------------------
% 2.89/1.45  Preprocessing        : 0.34
% 2.89/1.45  Parsing              : 0.18
% 2.89/1.45  CNF conversion       : 0.02
% 2.89/1.45  Main loop            : 0.34
% 2.89/1.45  Inferencing          : 0.14
% 2.89/1.45  Reduction            : 0.10
% 2.89/1.45  Demodulation         : 0.06
% 2.89/1.45  BG Simplification    : 0.02
% 2.89/1.45  Subsumption          : 0.06
% 2.89/1.45  Abstraction          : 0.02
% 2.89/1.45  MUC search           : 0.00
% 2.89/1.45  Cooper               : 0.00
% 2.89/1.45  Total                : 0.72
% 2.89/1.45  Index Insertion      : 0.00
% 2.89/1.45  Index Deletion       : 0.00
% 2.89/1.45  Index Matching       : 0.00
% 2.89/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
