%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:39 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 216 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1634,plain,(
    ! [A_165,B_166,C_167] :
      ( ~ r1_xboole_0(A_165,B_166)
      | ~ r2_hidden(C_167,B_166)
      | ~ r2_hidden(C_167,A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1644,plain,(
    ! [C_168,B_169,A_170] :
      ( ~ r2_hidden(C_168,B_169)
      | ~ r2_hidden(C_168,A_170)
      | k3_xboole_0(A_170,B_169) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1634])).

tff(c_1685,plain,(
    ! [A_178,B_179,A_180] :
      ( ~ r2_hidden('#skF_1'(A_178,B_179),A_180)
      | k3_xboole_0(A_180,A_178) != k1_xboole_0
      | r1_xboole_0(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_10,c_1644])).

tff(c_1719,plain,(
    ! [B_186,A_187] :
      ( k3_xboole_0(B_186,A_187) != k1_xboole_0
      | r1_xboole_0(A_187,B_186) ) ),
    inference(resolution,[status(thm)],[c_8,c_1685])).

tff(c_48,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_95,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7')
    | k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_131,plain,(
    k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_42])).

tff(c_1391,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(k4_tarski('#skF_3'(A_151,B_152),'#skF_2'(A_151,B_152)),A_151)
      | r2_hidden('#skF_4'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,B_42)
      | ~ r1_xboole_0(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_55,plain,(
    ! [A_41] : ~ r2_hidden(A_41,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_1473,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_155),B_155)
      | k2_relat_1(k1_xboole_0) = B_155 ) ),
    inference(resolution,[status(thm)],[c_1391,c_55])).

tff(c_1535,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1473,c_55])).

tff(c_40,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    k3_xboole_0(k2_relat_1('#skF_8'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_194,plain,(
    ! [B_71,A_72] :
      ( k10_relat_1(B_71,k3_xboole_0(k2_relat_1(B_71),A_72)) = k10_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_203,plain,
    ( k10_relat_1('#skF_8',k1_xboole_0) = k10_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_194])).

tff(c_211,plain,(
    k10_relat_1('#skF_8',k1_xboole_0) = k10_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_203])).

tff(c_290,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_6'(A_92,B_93,C_94),B_93)
      | ~ r2_hidden(A_92,k10_relat_1(C_94,B_93))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_307,plain,(
    ! [A_95,C_96] :
      ( ~ r2_hidden(A_95,k10_relat_1(C_96,k1_xboole_0))
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_290,c_55])).

tff(c_314,plain,(
    ! [A_95] :
      ( ~ r2_hidden(A_95,k10_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_307])).

tff(c_325,plain,(
    ! [A_95] : ~ r2_hidden(A_95,k10_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_314])).

tff(c_1530,plain,(
    k10_relat_1('#skF_8','#skF_7') = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1473,c_325])).

tff(c_1587,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1530])).

tff(c_1588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1587])).

tff(c_1590,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1733,plain,(
    k3_xboole_0('#skF_7',k2_relat_1('#skF_8')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1719,c_1590])).

tff(c_1589,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_18,plain,(
    ! [A_13,C_28] :
      ( r2_hidden(k4_tarski('#skF_5'(A_13,k2_relat_1(A_13),C_28),C_28),A_13)
      | ~ r2_hidden(C_28,k2_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2400,plain,(
    ! [A_228,C_229,B_230,D_231] :
      ( r2_hidden(A_228,k10_relat_1(C_229,B_230))
      | ~ r2_hidden(D_231,B_230)
      | ~ r2_hidden(k4_tarski(A_228,D_231),C_229)
      | ~ r2_hidden(D_231,k2_relat_1(C_229))
      | ~ v1_relat_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3451,plain,(
    ! [A_290,C_291,A_292,B_293] :
      ( r2_hidden(A_290,k10_relat_1(C_291,A_292))
      | ~ r2_hidden(k4_tarski(A_290,'#skF_1'(A_292,B_293)),C_291)
      | ~ r2_hidden('#skF_1'(A_292,B_293),k2_relat_1(C_291))
      | ~ v1_relat_1(C_291)
      | r1_xboole_0(A_292,B_293) ) ),
    inference(resolution,[status(thm)],[c_10,c_2400])).

tff(c_11331,plain,(
    ! [A_626,A_627,B_628] :
      ( r2_hidden('#skF_5'(A_626,k2_relat_1(A_626),'#skF_1'(A_627,B_628)),k10_relat_1(A_626,A_627))
      | ~ v1_relat_1(A_626)
      | r1_xboole_0(A_627,B_628)
      | ~ r2_hidden('#skF_1'(A_627,B_628),k2_relat_1(A_626)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3451])).

tff(c_11446,plain,(
    ! [B_628] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'('#skF_7',B_628)),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0('#skF_7',B_628)
      | ~ r2_hidden('#skF_1'('#skF_7',B_628),k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_11331])).

tff(c_11471,plain,(
    ! [B_628] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'('#skF_7',B_628)),k1_xboole_0)
      | r1_xboole_0('#skF_7',B_628)
      | ~ r2_hidden('#skF_1'('#skF_7',B_628),k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11446])).

tff(c_11473,plain,(
    ! [B_629] :
      ( r1_xboole_0('#skF_7',B_629)
      | ~ r2_hidden('#skF_1'('#skF_7',B_629),k2_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_11471])).

tff(c_11478,plain,(
    r1_xboole_0('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_8,c_11473])).

tff(c_11483,plain,(
    k3_xboole_0('#skF_7',k2_relat_1('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11478,c_2])).

tff(c_11488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1733,c_11483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.60/2.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.70  
% 7.60/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.71  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.60/2.71  
% 7.60/2.71  %Foreground sorts:
% 7.60/2.71  
% 7.60/2.71  
% 7.60/2.71  %Background operators:
% 7.60/2.71  
% 7.60/2.71  
% 7.60/2.71  %Foreground operators:
% 7.60/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.60/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.60/2.71  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.60/2.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.60/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.60/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.60/2.71  tff('#skF_7', type, '#skF_7': $i).
% 7.60/2.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.60/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.60/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.60/2.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.60/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.60/2.71  tff('#skF_8', type, '#skF_8': $i).
% 7.60/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.60/2.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.60/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.60/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.60/2.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.60/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.60/2.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.60/2.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.60/2.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.60/2.71  
% 7.60/2.72  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.60/2.72  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.60/2.72  tff(f_86, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 7.60/2.72  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 7.60/2.72  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.60/2.72  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 7.60/2.72  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 7.60/2.72  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 7.60/2.72  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.60/2.72  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.60/2.72  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.60/2.72  tff(c_1634, plain, (![A_165, B_166, C_167]: (~r1_xboole_0(A_165, B_166) | ~r2_hidden(C_167, B_166) | ~r2_hidden(C_167, A_165))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.60/2.72  tff(c_1644, plain, (![C_168, B_169, A_170]: (~r2_hidden(C_168, B_169) | ~r2_hidden(C_168, A_170) | k3_xboole_0(A_170, B_169)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1634])).
% 7.60/2.72  tff(c_1685, plain, (![A_178, B_179, A_180]: (~r2_hidden('#skF_1'(A_178, B_179), A_180) | k3_xboole_0(A_180, A_178)!=k1_xboole_0 | r1_xboole_0(A_178, B_179))), inference(resolution, [status(thm)], [c_10, c_1644])).
% 7.60/2.72  tff(c_1719, plain, (![B_186, A_187]: (k3_xboole_0(B_186, A_187)!=k1_xboole_0 | r1_xboole_0(A_187, B_186))), inference(resolution, [status(thm)], [c_8, c_1685])).
% 7.60/2.72  tff(c_48, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.60/2.72  tff(c_95, plain, (r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_48])).
% 7.60/2.72  tff(c_42, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7') | k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.60/2.72  tff(c_131, plain, (k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_42])).
% 7.60/2.72  tff(c_1391, plain, (![A_151, B_152]: (r2_hidden(k4_tarski('#skF_3'(A_151, B_152), '#skF_2'(A_151, B_152)), A_151) | r2_hidden('#skF_4'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.60/2.72  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.60/2.72  tff(c_50, plain, (![A_41, B_42]: (~r2_hidden(A_41, B_42) | ~r1_xboole_0(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.60/2.72  tff(c_55, plain, (![A_41]: (~r2_hidden(A_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_50])).
% 7.60/2.72  tff(c_1473, plain, (![B_155]: (r2_hidden('#skF_4'(k1_xboole_0, B_155), B_155) | k2_relat_1(k1_xboole_0)=B_155)), inference(resolution, [status(thm)], [c_1391, c_55])).
% 7.60/2.72  tff(c_1535, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1473, c_55])).
% 7.60/2.72  tff(c_40, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.60/2.72  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.60/2.72  tff(c_99, plain, (k3_xboole_0(k2_relat_1('#skF_8'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_2])).
% 7.60/2.72  tff(c_194, plain, (![B_71, A_72]: (k10_relat_1(B_71, k3_xboole_0(k2_relat_1(B_71), A_72))=k10_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.60/2.72  tff(c_203, plain, (k10_relat_1('#skF_8', k1_xboole_0)=k10_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_99, c_194])).
% 7.60/2.72  tff(c_211, plain, (k10_relat_1('#skF_8', k1_xboole_0)=k10_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_203])).
% 7.60/2.72  tff(c_290, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_6'(A_92, B_93, C_94), B_93) | ~r2_hidden(A_92, k10_relat_1(C_94, B_93)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.60/2.72  tff(c_307, plain, (![A_95, C_96]: (~r2_hidden(A_95, k10_relat_1(C_96, k1_xboole_0)) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_290, c_55])).
% 7.60/2.72  tff(c_314, plain, (![A_95]: (~r2_hidden(A_95, k10_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_307])).
% 7.60/2.72  tff(c_325, plain, (![A_95]: (~r2_hidden(A_95, k10_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_314])).
% 7.60/2.72  tff(c_1530, plain, (k10_relat_1('#skF_8', '#skF_7')=k2_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1473, c_325])).
% 7.60/2.72  tff(c_1587, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1530])).
% 7.60/2.72  tff(c_1588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_1587])).
% 7.60/2.72  tff(c_1590, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 7.60/2.72  tff(c_1733, plain, (k3_xboole_0('#skF_7', k2_relat_1('#skF_8'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1719, c_1590])).
% 7.60/2.72  tff(c_1589, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 7.60/2.72  tff(c_18, plain, (![A_13, C_28]: (r2_hidden(k4_tarski('#skF_5'(A_13, k2_relat_1(A_13), C_28), C_28), A_13) | ~r2_hidden(C_28, k2_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.60/2.72  tff(c_2400, plain, (![A_228, C_229, B_230, D_231]: (r2_hidden(A_228, k10_relat_1(C_229, B_230)) | ~r2_hidden(D_231, B_230) | ~r2_hidden(k4_tarski(A_228, D_231), C_229) | ~r2_hidden(D_231, k2_relat_1(C_229)) | ~v1_relat_1(C_229))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.60/2.72  tff(c_3451, plain, (![A_290, C_291, A_292, B_293]: (r2_hidden(A_290, k10_relat_1(C_291, A_292)) | ~r2_hidden(k4_tarski(A_290, '#skF_1'(A_292, B_293)), C_291) | ~r2_hidden('#skF_1'(A_292, B_293), k2_relat_1(C_291)) | ~v1_relat_1(C_291) | r1_xboole_0(A_292, B_293))), inference(resolution, [status(thm)], [c_10, c_2400])).
% 7.60/2.72  tff(c_11331, plain, (![A_626, A_627, B_628]: (r2_hidden('#skF_5'(A_626, k2_relat_1(A_626), '#skF_1'(A_627, B_628)), k10_relat_1(A_626, A_627)) | ~v1_relat_1(A_626) | r1_xboole_0(A_627, B_628) | ~r2_hidden('#skF_1'(A_627, B_628), k2_relat_1(A_626)))), inference(resolution, [status(thm)], [c_18, c_3451])).
% 7.60/2.72  tff(c_11446, plain, (![B_628]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'('#skF_7', B_628)), k1_xboole_0) | ~v1_relat_1('#skF_8') | r1_xboole_0('#skF_7', B_628) | ~r2_hidden('#skF_1'('#skF_7', B_628), k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1589, c_11331])).
% 7.60/2.72  tff(c_11471, plain, (![B_628]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'('#skF_7', B_628)), k1_xboole_0) | r1_xboole_0('#skF_7', B_628) | ~r2_hidden('#skF_1'('#skF_7', B_628), k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_11446])).
% 7.60/2.72  tff(c_11473, plain, (![B_629]: (r1_xboole_0('#skF_7', B_629) | ~r2_hidden('#skF_1'('#skF_7', B_629), k2_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_55, c_11471])).
% 7.60/2.72  tff(c_11478, plain, (r1_xboole_0('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_8, c_11473])).
% 7.60/2.72  tff(c_11483, plain, (k3_xboole_0('#skF_7', k2_relat_1('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_11478, c_2])).
% 7.60/2.72  tff(c_11488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1733, c_11483])).
% 7.60/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.72  
% 7.60/2.72  Inference rules
% 7.60/2.72  ----------------------
% 7.60/2.72  #Ref     : 0
% 7.60/2.72  #Sup     : 2656
% 7.60/2.72  #Fact    : 0
% 7.60/2.72  #Define  : 0
% 7.60/2.72  #Split   : 4
% 7.60/2.72  #Chain   : 0
% 7.60/2.72  #Close   : 0
% 7.60/2.72  
% 7.60/2.72  Ordering : KBO
% 7.60/2.72  
% 7.60/2.72  Simplification rules
% 7.60/2.72  ----------------------
% 7.60/2.72  #Subsume      : 863
% 7.60/2.72  #Demod        : 1389
% 7.60/2.72  #Tautology    : 964
% 7.60/2.72  #SimpNegUnit  : 80
% 7.60/2.72  #BackRed      : 38
% 7.60/2.72  
% 7.60/2.72  #Partial instantiations: 0
% 7.60/2.72  #Strategies tried      : 1
% 7.60/2.72  
% 7.60/2.72  Timing (in seconds)
% 7.60/2.72  ----------------------
% 7.70/2.72  Preprocessing        : 0.31
% 7.70/2.72  Parsing              : 0.17
% 7.70/2.72  CNF conversion       : 0.02
% 7.70/2.72  Main loop            : 1.72
% 7.70/2.72  Inferencing          : 0.56
% 7.70/2.72  Reduction            : 0.43
% 7.70/2.72  Demodulation         : 0.28
% 7.70/2.72  BG Simplification    : 0.05
% 7.71/2.72  Subsumption          : 0.57
% 7.71/2.72  Abstraction          : 0.07
% 7.71/2.72  MUC search           : 0.00
% 7.71/2.72  Cooper               : 0.00
% 7.71/2.72  Total                : 2.06
% 7.71/2.72  Index Insertion      : 0.00
% 7.71/2.72  Index Deletion       : 0.00
% 7.71/2.72  Index Matching       : 0.00
% 7.71/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
