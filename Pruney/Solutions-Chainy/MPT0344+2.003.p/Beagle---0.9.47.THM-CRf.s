%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 247 expanded)
%              Number of leaves         :   30 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  164 ( 582 expanded)
%              Number of equality atoms :   28 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,A_34)
      | ~ v1_xboole_0(B_35)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_127,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(B_56,A_57)
      | ~ m1_subset_1(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_9')
      | ~ m1_subset_1(C_37,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_137,plain,(
    ! [B_56] :
      ( ~ m1_subset_1(B_56,'#skF_8')
      | ~ m1_subset_1(B_56,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_127,c_60])).

tff(c_199,plain,(
    ! [B_68] :
      ( ~ m1_subset_1(B_68,'#skF_8')
      | ~ m1_subset_1(B_68,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_204,plain,(
    ! [B_35] :
      ( ~ m1_subset_1(B_35,'#skF_8')
      | ~ v1_xboole_0(B_35)
      | ~ v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_199])).

tff(c_205,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_10,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_91,plain,(
    ! [C_46] :
      ( ~ r2_hidden(C_46,'#skF_9')
      | ~ m1_subset_1(C_46,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_95,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_98,plain,(
    ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_95])).

tff(c_138,plain,(
    ! [B_58,A_59] :
      ( m1_subset_1(B_58,A_59)
      | ~ r2_hidden(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_150,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1'(A_4),A_4)
      | v1_xboole_0(A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_106,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ v1_xboole_0(B_50)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_110,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_9'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_106,c_98])).

tff(c_111,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_117,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_125,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_126,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_20,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1438,plain,(
    ! [B_152,A_153] :
      ( r1_tarski(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | v1_xboole_0(k1_zfmisc_1(A_153)) ) ),
    inference(resolution,[status(thm)],[c_127,c_20])).

tff(c_1452,plain,
    ( r1_tarski('#skF_9','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_1438])).

tff(c_1460,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_1452])).

tff(c_54,plain,(
    ! [B_35,A_34] :
      ( r2_hidden(B_35,A_34)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_33] : k3_tarski(k1_zfmisc_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_187,plain,(
    ! [C_65,A_66,D_67] :
      ( r2_hidden(C_65,k3_tarski(A_66))
      | ~ r2_hidden(D_67,A_66)
      | ~ r2_hidden(C_65,D_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,(
    ! [C_65,A_9,C_13] :
      ( r2_hidden(C_65,k3_tarski(k1_zfmisc_1(A_9)))
      | ~ r2_hidden(C_65,C_13)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_22,c_187])).

tff(c_1366,plain,(
    ! [C_145,A_146,C_147] :
      ( r2_hidden(C_145,A_146)
      | ~ r2_hidden(C_145,C_147)
      | ~ r1_tarski(C_147,A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191])).

tff(c_1685,plain,(
    ! [B_180,A_181,A_182] :
      ( r2_hidden(B_180,A_181)
      | ~ r1_tarski(A_182,A_181)
      | ~ m1_subset_1(B_180,A_182)
      | v1_xboole_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_54,c_1366])).

tff(c_1691,plain,(
    ! [B_180] :
      ( r2_hidden(B_180,'#skF_8')
      | ~ m1_subset_1(B_180,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1460,c_1685])).

tff(c_1709,plain,(
    ! [B_183] :
      ( r2_hidden(B_183,'#skF_8')
      | ~ m1_subset_1(B_183,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_1691])).

tff(c_52,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,A_34)
      | ~ r2_hidden(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1719,plain,(
    ! [B_183] :
      ( m1_subset_1(B_183,'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(B_183,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1709,c_52])).

tff(c_1726,plain,(
    ! [B_184] :
      ( m1_subset_1(B_184,'#skF_8')
      | ~ m1_subset_1(B_184,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1719])).

tff(c_1730,plain,
    ( m1_subset_1('#skF_1'('#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_150,c_1726])).

tff(c_1738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_205,c_98,c_1730])).

tff(c_1740,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1743,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1740,c_8])).

tff(c_1747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1743])).

tff(c_1748,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_1762,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1748,c_8])).

tff(c_1766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1762])).

tff(c_1768,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_1772,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1768,c_8])).

tff(c_1777,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_62])).

tff(c_1812,plain,(
    ! [B_191,A_192] :
      ( v1_xboole_0(B_191)
      | ~ m1_subset_1(B_191,A_192)
      | ~ v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1820,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_1812])).

tff(c_1821,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1820])).

tff(c_1836,plain,(
    ! [B_197,A_198] :
      ( r2_hidden(B_197,A_198)
      | ~ m1_subset_1(B_197,A_198)
      | v1_xboole_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2104,plain,(
    ! [B_226,A_227] :
      ( r1_tarski(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(A_227))
      | v1_xboole_0(k1_zfmisc_1(A_227)) ) ),
    inference(resolution,[status(thm)],[c_1836,c_20])).

tff(c_2118,plain,
    ( r1_tarski('#skF_9','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_2104])).

tff(c_2126,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1821,c_2118])).

tff(c_18,plain,(
    ! [A_8] :
      ( r2_xboole_0(k1_xboole_0,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ r2_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_1773,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_8',A_8)
      | A_8 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_1772,c_90])).

tff(c_1851,plain,(
    ! [B_199,A_200] :
      ( B_199 = A_200
      | ~ r1_tarski(B_199,A_200)
      | ~ r1_tarski(A_200,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1856,plain,(
    ! [A_8] :
      ( ~ r1_tarski(A_8,'#skF_8')
      | A_8 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1773,c_1851])).

tff(c_2129,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2126,c_1856])).

tff(c_2135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1777,c_2129])).

tff(c_2136,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1820])).

tff(c_1776,plain,(
    ! [A_3] :
      ( A_3 = '#skF_8'
      | ~ v1_xboole_0(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_8])).

tff(c_2140,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2136,c_1776])).

tff(c_2144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1777,c_2140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.58  
% 3.46/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.59  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 3.46/1.59  
% 3.46/1.59  %Foreground sorts:
% 3.46/1.59  
% 3.46/1.59  
% 3.46/1.59  %Background operators:
% 3.46/1.59  
% 3.46/1.59  
% 3.46/1.59  %Foreground operators:
% 3.46/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.46/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.46/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.46/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.59  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.46/1.59  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.46/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.46/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.46/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.46/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.59  
% 3.46/1.60  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.46/1.60  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.46/1.60  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.46/1.60  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.46/1.60  tff(f_74, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.46/1.60  tff(f_72, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 3.46/1.60  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.46/1.60  tff(f_55, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 3.46/1.60  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.46/1.60  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.60  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.46/1.60  tff(c_56, plain, (![B_35, A_34]: (m1_subset_1(B_35, A_34) | ~v1_xboole_0(B_35) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_127, plain, (![B_56, A_57]: (r2_hidden(B_56, A_57) | ~m1_subset_1(B_56, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_60, plain, (![C_37]: (~r2_hidden(C_37, '#skF_9') | ~m1_subset_1(C_37, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.46/1.60  tff(c_137, plain, (![B_56]: (~m1_subset_1(B_56, '#skF_8') | ~m1_subset_1(B_56, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_127, c_60])).
% 3.46/1.60  tff(c_199, plain, (![B_68]: (~m1_subset_1(B_68, '#skF_8') | ~m1_subset_1(B_68, '#skF_9'))), inference(splitLeft, [status(thm)], [c_137])).
% 3.46/1.60  tff(c_204, plain, (![B_35]: (~m1_subset_1(B_35, '#skF_8') | ~v1_xboole_0(B_35) | ~v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_199])).
% 3.46/1.60  tff(c_205, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_204])).
% 3.46/1.60  tff(c_10, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.46/1.60  tff(c_91, plain, (![C_46]: (~r2_hidden(C_46, '#skF_9') | ~m1_subset_1(C_46, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.46/1.60  tff(c_95, plain, (~m1_subset_1('#skF_1'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_10, c_91])).
% 3.46/1.60  tff(c_98, plain, (~m1_subset_1('#skF_1'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_95])).
% 3.46/1.60  tff(c_138, plain, (![B_58, A_59]: (m1_subset_1(B_58, A_59) | ~r2_hidden(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_150, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4) | v1_xboole_0(A_4) | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_10, c_138])).
% 3.46/1.60  tff(c_106, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~v1_xboole_0(B_50) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_110, plain, (~v1_xboole_0('#skF_1'('#skF_9')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_106, c_98])).
% 3.46/1.60  tff(c_111, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_110])).
% 3.46/1.60  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.46/1.60  tff(c_117, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_125, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_117])).
% 3.46/1.60  tff(c_126, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_125])).
% 3.46/1.60  tff(c_20, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.46/1.60  tff(c_1438, plain, (![B_152, A_153]: (r1_tarski(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | v1_xboole_0(k1_zfmisc_1(A_153)))), inference(resolution, [status(thm)], [c_127, c_20])).
% 3.46/1.60  tff(c_1452, plain, (r1_tarski('#skF_9', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_1438])).
% 3.46/1.60  tff(c_1460, plain, (r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_126, c_1452])).
% 3.46/1.60  tff(c_54, plain, (![B_35, A_34]: (r2_hidden(B_35, A_34) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_50, plain, (![A_33]: (k3_tarski(k1_zfmisc_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.60  tff(c_22, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.46/1.60  tff(c_187, plain, (![C_65, A_66, D_67]: (r2_hidden(C_65, k3_tarski(A_66)) | ~r2_hidden(D_67, A_66) | ~r2_hidden(C_65, D_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.46/1.60  tff(c_191, plain, (![C_65, A_9, C_13]: (r2_hidden(C_65, k3_tarski(k1_zfmisc_1(A_9))) | ~r2_hidden(C_65, C_13) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_22, c_187])).
% 3.46/1.60  tff(c_1366, plain, (![C_145, A_146, C_147]: (r2_hidden(C_145, A_146) | ~r2_hidden(C_145, C_147) | ~r1_tarski(C_147, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191])).
% 3.46/1.60  tff(c_1685, plain, (![B_180, A_181, A_182]: (r2_hidden(B_180, A_181) | ~r1_tarski(A_182, A_181) | ~m1_subset_1(B_180, A_182) | v1_xboole_0(A_182))), inference(resolution, [status(thm)], [c_54, c_1366])).
% 3.46/1.60  tff(c_1691, plain, (![B_180]: (r2_hidden(B_180, '#skF_8') | ~m1_subset_1(B_180, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_1460, c_1685])).
% 3.46/1.60  tff(c_1709, plain, (![B_183]: (r2_hidden(B_183, '#skF_8') | ~m1_subset_1(B_183, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_205, c_1691])).
% 3.46/1.60  tff(c_52, plain, (![B_35, A_34]: (m1_subset_1(B_35, A_34) | ~r2_hidden(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_1719, plain, (![B_183]: (m1_subset_1(B_183, '#skF_8') | v1_xboole_0('#skF_8') | ~m1_subset_1(B_183, '#skF_9'))), inference(resolution, [status(thm)], [c_1709, c_52])).
% 3.46/1.60  tff(c_1726, plain, (![B_184]: (m1_subset_1(B_184, '#skF_8') | ~m1_subset_1(B_184, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_111, c_1719])).
% 3.46/1.60  tff(c_1730, plain, (m1_subset_1('#skF_1'('#skF_9'), '#skF_8') | v1_xboole_0('#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_150, c_1726])).
% 3.46/1.60  tff(c_1738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_205, c_98, c_1730])).
% 3.46/1.60  tff(c_1740, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_204])).
% 3.46/1.60  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.46/1.60  tff(c_1743, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1740, c_8])).
% 3.46/1.60  tff(c_1747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1743])).
% 3.46/1.60  tff(c_1748, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_125])).
% 3.46/1.60  tff(c_1762, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1748, c_8])).
% 3.46/1.60  tff(c_1766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1762])).
% 3.46/1.60  tff(c_1768, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_110])).
% 3.46/1.60  tff(c_1772, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1768, c_8])).
% 3.46/1.60  tff(c_1777, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_62])).
% 3.46/1.60  tff(c_1812, plain, (![B_191, A_192]: (v1_xboole_0(B_191) | ~m1_subset_1(B_191, A_192) | ~v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_1820, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_1812])).
% 3.46/1.60  tff(c_1821, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1820])).
% 3.46/1.60  tff(c_1836, plain, (![B_197, A_198]: (r2_hidden(B_197, A_198) | ~m1_subset_1(B_197, A_198) | v1_xboole_0(A_198))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_2104, plain, (![B_226, A_227]: (r1_tarski(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(A_227)) | v1_xboole_0(k1_zfmisc_1(A_227)))), inference(resolution, [status(thm)], [c_1836, c_20])).
% 3.46/1.60  tff(c_2118, plain, (r1_tarski('#skF_9', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_2104])).
% 3.46/1.60  tff(c_2126, plain, (r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1821, c_2118])).
% 3.46/1.60  tff(c_18, plain, (![A_8]: (r2_xboole_0(k1_xboole_0, A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.60  tff(c_86, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~r2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.60  tff(c_90, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_18, c_86])).
% 3.46/1.60  tff(c_1773, plain, (![A_8]: (r1_tarski('#skF_8', A_8) | A_8='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_1772, c_90])).
% 3.46/1.60  tff(c_1851, plain, (![B_199, A_200]: (B_199=A_200 | ~r1_tarski(B_199, A_200) | ~r1_tarski(A_200, B_199))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.60  tff(c_1856, plain, (![A_8]: (~r1_tarski(A_8, '#skF_8') | A_8='#skF_8')), inference(resolution, [status(thm)], [c_1773, c_1851])).
% 3.46/1.60  tff(c_2129, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2126, c_1856])).
% 3.46/1.60  tff(c_2135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1777, c_2129])).
% 3.46/1.60  tff(c_2136, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1820])).
% 3.46/1.60  tff(c_1776, plain, (![A_3]: (A_3='#skF_8' | ~v1_xboole_0(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_8])).
% 3.46/1.60  tff(c_2140, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2136, c_1776])).
% 3.46/1.60  tff(c_2144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1777, c_2140])).
% 3.46/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.60  
% 3.46/1.60  Inference rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Ref     : 0
% 3.46/1.60  #Sup     : 438
% 3.46/1.60  #Fact    : 0
% 3.46/1.60  #Define  : 0
% 3.46/1.60  #Split   : 17
% 3.46/1.60  #Chain   : 0
% 3.46/1.60  #Close   : 0
% 3.46/1.60  
% 3.46/1.60  Ordering : KBO
% 3.46/1.60  
% 3.46/1.60  Simplification rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Subsume      : 69
% 3.46/1.60  #Demod        : 141
% 3.46/1.60  #Tautology    : 116
% 3.46/1.60  #SimpNegUnit  : 48
% 3.46/1.60  #BackRed      : 9
% 3.46/1.60  
% 3.46/1.60  #Partial instantiations: 0
% 3.46/1.60  #Strategies tried      : 1
% 3.46/1.60  
% 3.46/1.60  Timing (in seconds)
% 3.46/1.60  ----------------------
% 3.46/1.61  Preprocessing        : 0.30
% 3.46/1.61  Parsing              : 0.16
% 3.46/1.61  CNF conversion       : 0.02
% 3.46/1.61  Main loop            : 0.53
% 3.46/1.61  Inferencing          : 0.19
% 3.46/1.61  Reduction            : 0.15
% 3.46/1.61  Demodulation         : 0.10
% 3.46/1.61  BG Simplification    : 0.02
% 3.46/1.61  Subsumption          : 0.12
% 3.46/1.61  Abstraction          : 0.03
% 3.46/1.61  MUC search           : 0.00
% 3.46/1.61  Cooper               : 0.00
% 3.46/1.61  Total                : 0.87
% 3.46/1.61  Index Insertion      : 0.00
% 3.46/1.61  Index Deletion       : 0.00
% 3.46/1.61  Index Matching       : 0.00
% 3.46/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
