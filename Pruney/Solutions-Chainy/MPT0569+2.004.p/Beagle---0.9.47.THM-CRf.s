%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:36 EST 2020

% Result     : Theorem 30.41s
% Output     : CNFRefutation 30.53s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 109 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 205 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_13 > #skF_2 > #skF_8 > #skF_11 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_100,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_72,plain,
    ( k10_relat_1('#skF_13','#skF_12') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_96,plain,(
    r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12')
    | k10_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_98,plain,(
    k10_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66])).

tff(c_62,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2008,plain,(
    ! [A_301,B_302] :
      ( r2_hidden(k4_tarski('#skF_6'(A_301,B_302),'#skF_7'(A_301,B_302)),A_301)
      | r2_hidden('#skF_8'(A_301,B_302),B_302)
      | k1_relat_1(A_301) = B_302 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden(A_84,B_85)
      | ~ r1_xboole_0(k1_tarski(A_84),B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    ! [A_84] : ~ r2_hidden(A_84,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_2145,plain,(
    ! [B_302] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_302),B_302)
      | k1_relat_1(k1_xboole_0) = B_302 ) ),
    inference(resolution,[status(thm)],[c_2008,c_87])).

tff(c_2182,plain,(
    ! [B_303] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_303),B_303)
      | k1_xboole_0 = B_303 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2145])).

tff(c_64,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_11'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k10_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_573,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_11'(A_175,B_176,C_177),k2_relat_1(C_177))
      | ~ r2_hidden(A_175,k10_relat_1(C_177,B_176))
      | ~ v1_relat_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,B_94)
      | ~ r2_hidden(C_95,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    ! [C_95] :
      ( ~ r2_hidden(C_95,'#skF_12')
      | ~ r2_hidden(C_95,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_96,c_120])).

tff(c_577,plain,(
    ! [A_175,B_176] :
      ( ~ r2_hidden('#skF_11'(A_175,B_176,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_175,k10_relat_1('#skF_13',B_176))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_573,c_128])).

tff(c_624,plain,(
    ! [A_184,B_185] :
      ( ~ r2_hidden('#skF_11'(A_184,B_185,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_184,k10_relat_1('#skF_13',B_185)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_577])).

tff(c_628,plain,(
    ! [A_77] :
      ( ~ r2_hidden(A_77,k10_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_54,c_624])).

tff(c_631,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k10_relat_1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_628])).

tff(c_2264,plain,(
    k10_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2182,c_631])).

tff(c_2340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2264])).

tff(c_2342,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_76] :
      ( k9_relat_1(A_76,k1_relat_1(A_76)) = k2_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2341,plain,(
    k10_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_46,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_10'(A_70,B_71,C_72),A_70),C_72)
      | ~ r2_hidden(A_70,k9_relat_1(C_72,B_71))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2787,plain,(
    ! [D_375,A_376,B_377,E_378] :
      ( r2_hidden(D_375,k10_relat_1(A_376,B_377))
      | ~ r2_hidden(E_378,B_377)
      | ~ r2_hidden(k4_tarski(D_375,E_378),A_376)
      | ~ v1_relat_1(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6332,plain,(
    ! [D_561,A_562,A_563,B_564] :
      ( r2_hidden(D_561,k10_relat_1(A_562,A_563))
      | ~ r2_hidden(k4_tarski(D_561,'#skF_1'(A_563,B_564)),A_562)
      | ~ v1_relat_1(A_562)
      | r1_xboole_0(A_563,B_564) ) ),
    inference(resolution,[status(thm)],[c_6,c_2787])).

tff(c_57180,plain,(
    ! [A_1742,B_1743,B_1744,C_1745] :
      ( r2_hidden('#skF_10'('#skF_1'(A_1742,B_1743),B_1744,C_1745),k10_relat_1(C_1745,A_1742))
      | r1_xboole_0(A_1742,B_1743)
      | ~ r2_hidden('#skF_1'(A_1742,B_1743),k9_relat_1(C_1745,B_1744))
      | ~ v1_relat_1(C_1745) ) ),
    inference(resolution,[status(thm)],[c_46,c_6332])).

tff(c_57316,plain,(
    ! [B_1743,B_1744] :
      ( r2_hidden('#skF_10'('#skF_1'('#skF_12',B_1743),B_1744,'#skF_13'),k1_xboole_0)
      | r1_xboole_0('#skF_12',B_1743)
      | ~ r2_hidden('#skF_1'('#skF_12',B_1743),k9_relat_1('#skF_13',B_1744))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2341,c_57180])).

tff(c_57358,plain,(
    ! [B_1743,B_1744] :
      ( r2_hidden('#skF_10'('#skF_1'('#skF_12',B_1743),B_1744,'#skF_13'),k1_xboole_0)
      | r1_xboole_0('#skF_12',B_1743)
      | ~ r2_hidden('#skF_1'('#skF_12',B_1743),k9_relat_1('#skF_13',B_1744)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_57316])).

tff(c_57360,plain,(
    ! [B_1746,B_1747] :
      ( r1_xboole_0('#skF_12',B_1746)
      | ~ r2_hidden('#skF_1'('#skF_12',B_1746),k9_relat_1('#skF_13',B_1747)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_57358])).

tff(c_57477,plain,(
    ! [B_1748] : r1_xboole_0('#skF_12',k9_relat_1('#skF_13',B_1748)) ),
    inference(resolution,[status(thm)],[c_4,c_57360])).

tff(c_57549,plain,
    ( r1_xboole_0('#skF_12',k2_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_57477])).

tff(c_57585,plain,(
    r1_xboole_0('#skF_12',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_57549])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57685,plain,(
    ! [C_1751] :
      ( ~ r2_hidden(C_1751,k2_relat_1('#skF_13'))
      | ~ r2_hidden(C_1751,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_57585,c_2])).

tff(c_58475,plain,(
    ! [B_1759] :
      ( ~ r2_hidden('#skF_1'(k2_relat_1('#skF_13'),B_1759),'#skF_12')
      | r1_xboole_0(k2_relat_1('#skF_13'),B_1759) ) ),
    inference(resolution,[status(thm)],[c_6,c_57685])).

tff(c_58479,plain,(
    r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_58475])).

tff(c_58483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2342,c_2342,c_58479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.41/21.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.41/21.09  
% 30.41/21.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.53/21.09  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_13 > #skF_2 > #skF_8 > #skF_11 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1 > #skF_12 > #skF_10
% 30.53/21.09  
% 30.53/21.09  %Foreground sorts:
% 30.53/21.09  
% 30.53/21.09  
% 30.53/21.09  %Background operators:
% 30.53/21.09  
% 30.53/21.09  
% 30.53/21.09  %Foreground operators:
% 30.53/21.09  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 30.53/21.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.53/21.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.53/21.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 30.53/21.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 30.53/21.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.53/21.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 30.53/21.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.53/21.09  tff('#skF_13', type, '#skF_13': $i).
% 30.53/21.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 30.53/21.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 30.53/21.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.53/21.09  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 30.53/21.09  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 30.53/21.09  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 30.53/21.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.53/21.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 30.53/21.09  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 30.53/21.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.53/21.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 30.53/21.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.53/21.09  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 30.53/21.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.53/21.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.53/21.09  tff('#skF_12', type, '#skF_12': $i).
% 30.53/21.09  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 30.53/21.09  
% 30.53/21.11  tff(f_107, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 30.53/21.11  tff(f_100, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 30.53/21.11  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 30.53/21.11  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 30.53/21.11  tff(f_50, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 30.53/21.11  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 30.53/21.11  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 30.53/21.11  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 30.53/21.11  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 30.53/21.11  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 30.53/21.11  tff(c_72, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_107])).
% 30.53/21.11  tff(c_96, plain, (r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(splitLeft, [status(thm)], [c_72])).
% 30.53/21.11  tff(c_66, plain, (~r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12') | k10_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 30.53/21.11  tff(c_98, plain, (k10_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66])).
% 30.53/21.11  tff(c_62, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 30.53/21.11  tff(c_2008, plain, (![A_301, B_302]: (r2_hidden(k4_tarski('#skF_6'(A_301, B_302), '#skF_7'(A_301, B_302)), A_301) | r2_hidden('#skF_8'(A_301, B_302), B_302) | k1_relat_1(A_301)=B_302)), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.53/21.11  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.53/21.11  tff(c_82, plain, (![A_84, B_85]: (~r2_hidden(A_84, B_85) | ~r1_xboole_0(k1_tarski(A_84), B_85))), inference(cnfTransformation, [status(thm)], [f_50])).
% 30.53/21.11  tff(c_87, plain, (![A_84]: (~r2_hidden(A_84, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_82])).
% 30.53/21.11  tff(c_2145, plain, (![B_302]: (r2_hidden('#skF_8'(k1_xboole_0, B_302), B_302) | k1_relat_1(k1_xboole_0)=B_302)), inference(resolution, [status(thm)], [c_2008, c_87])).
% 30.53/21.11  tff(c_2182, plain, (![B_303]: (r2_hidden('#skF_8'(k1_xboole_0, B_303), B_303) | k1_xboole_0=B_303)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2145])).
% 30.53/21.11  tff(c_64, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_107])).
% 30.53/21.11  tff(c_54, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_11'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k10_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.53/21.11  tff(c_573, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_11'(A_175, B_176, C_177), k2_relat_1(C_177)) | ~r2_hidden(A_175, k10_relat_1(C_177, B_176)) | ~v1_relat_1(C_177))), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.53/21.11  tff(c_120, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, B_94) | ~r2_hidden(C_95, A_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.53/21.11  tff(c_128, plain, (![C_95]: (~r2_hidden(C_95, '#skF_12') | ~r2_hidden(C_95, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_96, c_120])).
% 30.53/21.11  tff(c_577, plain, (![A_175, B_176]: (~r2_hidden('#skF_11'(A_175, B_176, '#skF_13'), '#skF_12') | ~r2_hidden(A_175, k10_relat_1('#skF_13', B_176)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_573, c_128])).
% 30.53/21.11  tff(c_624, plain, (![A_184, B_185]: (~r2_hidden('#skF_11'(A_184, B_185, '#skF_13'), '#skF_12') | ~r2_hidden(A_184, k10_relat_1('#skF_13', B_185)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_577])).
% 30.53/21.11  tff(c_628, plain, (![A_77]: (~r2_hidden(A_77, k10_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_54, c_624])).
% 30.53/21.11  tff(c_631, plain, (![A_77]: (~r2_hidden(A_77, k10_relat_1('#skF_13', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_628])).
% 30.53/21.11  tff(c_2264, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_2182, c_631])).
% 30.53/21.11  tff(c_2340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2264])).
% 30.53/21.11  tff(c_2342, plain, (~r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(splitRight, [status(thm)], [c_72])).
% 30.53/21.11  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.53/21.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.53/21.11  tff(c_50, plain, (![A_76]: (k9_relat_1(A_76, k1_relat_1(A_76))=k2_relat_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_86])).
% 30.53/21.11  tff(c_2341, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 30.53/21.11  tff(c_46, plain, (![A_70, B_71, C_72]: (r2_hidden(k4_tarski('#skF_10'(A_70, B_71, C_72), A_70), C_72) | ~r2_hidden(A_70, k9_relat_1(C_72, B_71)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_82])).
% 30.53/21.11  tff(c_2787, plain, (![D_375, A_376, B_377, E_378]: (r2_hidden(D_375, k10_relat_1(A_376, B_377)) | ~r2_hidden(E_378, B_377) | ~r2_hidden(k4_tarski(D_375, E_378), A_376) | ~v1_relat_1(A_376))), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.53/21.11  tff(c_6332, plain, (![D_561, A_562, A_563, B_564]: (r2_hidden(D_561, k10_relat_1(A_562, A_563)) | ~r2_hidden(k4_tarski(D_561, '#skF_1'(A_563, B_564)), A_562) | ~v1_relat_1(A_562) | r1_xboole_0(A_563, B_564))), inference(resolution, [status(thm)], [c_6, c_2787])).
% 30.53/21.11  tff(c_57180, plain, (![A_1742, B_1743, B_1744, C_1745]: (r2_hidden('#skF_10'('#skF_1'(A_1742, B_1743), B_1744, C_1745), k10_relat_1(C_1745, A_1742)) | r1_xboole_0(A_1742, B_1743) | ~r2_hidden('#skF_1'(A_1742, B_1743), k9_relat_1(C_1745, B_1744)) | ~v1_relat_1(C_1745))), inference(resolution, [status(thm)], [c_46, c_6332])).
% 30.53/21.11  tff(c_57316, plain, (![B_1743, B_1744]: (r2_hidden('#skF_10'('#skF_1'('#skF_12', B_1743), B_1744, '#skF_13'), k1_xboole_0) | r1_xboole_0('#skF_12', B_1743) | ~r2_hidden('#skF_1'('#skF_12', B_1743), k9_relat_1('#skF_13', B_1744)) | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_2341, c_57180])).
% 30.53/21.11  tff(c_57358, plain, (![B_1743, B_1744]: (r2_hidden('#skF_10'('#skF_1'('#skF_12', B_1743), B_1744, '#skF_13'), k1_xboole_0) | r1_xboole_0('#skF_12', B_1743) | ~r2_hidden('#skF_1'('#skF_12', B_1743), k9_relat_1('#skF_13', B_1744)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_57316])).
% 30.53/21.11  tff(c_57360, plain, (![B_1746, B_1747]: (r1_xboole_0('#skF_12', B_1746) | ~r2_hidden('#skF_1'('#skF_12', B_1746), k9_relat_1('#skF_13', B_1747)))), inference(negUnitSimplification, [status(thm)], [c_87, c_57358])).
% 30.53/21.11  tff(c_57477, plain, (![B_1748]: (r1_xboole_0('#skF_12', k9_relat_1('#skF_13', B_1748)))), inference(resolution, [status(thm)], [c_4, c_57360])).
% 30.53/21.11  tff(c_57549, plain, (r1_xboole_0('#skF_12', k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_50, c_57477])).
% 30.53/21.11  tff(c_57585, plain, (r1_xboole_0('#skF_12', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_57549])).
% 30.53/21.11  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.53/21.11  tff(c_57685, plain, (![C_1751]: (~r2_hidden(C_1751, k2_relat_1('#skF_13')) | ~r2_hidden(C_1751, '#skF_12'))), inference(resolution, [status(thm)], [c_57585, c_2])).
% 30.53/21.11  tff(c_58475, plain, (![B_1759]: (~r2_hidden('#skF_1'(k2_relat_1('#skF_13'), B_1759), '#skF_12') | r1_xboole_0(k2_relat_1('#skF_13'), B_1759))), inference(resolution, [status(thm)], [c_6, c_57685])).
% 30.53/21.11  tff(c_58479, plain, (r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_4, c_58475])).
% 30.53/21.11  tff(c_58483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2342, c_2342, c_58479])).
% 30.53/21.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.53/21.11  
% 30.53/21.11  Inference rules
% 30.53/21.11  ----------------------
% 30.53/21.11  #Ref     : 0
% 30.53/21.11  #Sup     : 14739
% 30.53/21.11  #Fact    : 0
% 30.53/21.11  #Define  : 0
% 30.53/21.11  #Split   : 21
% 30.53/21.11  #Chain   : 0
% 30.53/21.11  #Close   : 0
% 30.53/21.11  
% 30.53/21.11  Ordering : KBO
% 30.53/21.11  
% 30.53/21.11  Simplification rules
% 30.53/21.11  ----------------------
% 30.53/21.11  #Subsume      : 6797
% 30.53/21.11  #Demod        : 4711
% 30.53/21.11  #Tautology    : 1733
% 30.53/21.11  #SimpNegUnit  : 809
% 30.53/21.11  #BackRed      : 0
% 30.53/21.11  
% 30.53/21.11  #Partial instantiations: 0
% 30.53/21.11  #Strategies tried      : 1
% 30.53/21.11  
% 30.53/21.11  Timing (in seconds)
% 30.53/21.11  ----------------------
% 30.53/21.11  Preprocessing        : 0.34
% 30.53/21.11  Parsing              : 0.18
% 30.53/21.11  CNF conversion       : 0.03
% 30.53/21.11  Main loop            : 19.97
% 30.53/21.11  Inferencing          : 1.99
% 30.53/21.11  Reduction            : 1.85
% 30.53/21.11  Demodulation         : 1.18
% 30.53/21.11  BG Simplification    : 0.16
% 30.53/21.11  Subsumption          : 15.49
% 30.53/21.11  Abstraction          : 0.26
% 30.53/21.11  MUC search           : 0.00
% 30.53/21.11  Cooper               : 0.00
% 30.53/21.11  Total                : 20.34
% 30.53/21.11  Index Insertion      : 0.00
% 30.53/21.11  Index Deletion       : 0.00
% 30.53/21.11  Index Matching       : 0.00
% 30.53/21.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
