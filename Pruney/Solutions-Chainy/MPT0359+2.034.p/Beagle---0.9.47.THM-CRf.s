%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:13 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 141 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 207 expanded)
%              Number of equality atoms :   32 (  75 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_74,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    ! [A_31] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_142,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,A_47)
      | ~ m1_subset_1(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_146,plain,(
    ! [B_46,A_16] :
      ( r1_tarski(B_46,A_16)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_142,c_34])).

tff(c_150,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_146])).

tff(c_164,plain,(
    ! [A_31] : r1_tarski(k1_xboole_0,A_31) ),
    inference(resolution,[status(thm)],[c_66,c_150])).

tff(c_54,plain,(
    ! [A_23] : k1_subset_1(A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_subset_1(A_30)) = k2_subset_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_subset_1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_64])).

tff(c_80,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_78])).

tff(c_277,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_286,plain,(
    ! [A_31] : k3_subset_1(A_31,k3_subset_1(A_31,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_277])).

tff(c_291,plain,(
    ! [A_31] : k3_subset_1(A_31,A_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_286])).

tff(c_70,plain,
    ( k2_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_77,plain,
    ( '#skF_7' != '#skF_6'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_70])).

tff(c_124,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_76,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | k2_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76])).

tff(c_125,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_79])).

tff(c_126,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_125,c_124])).

tff(c_292,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_126])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_292])).

tff(c_296,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_297,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_439,plain,(
    ! [C_103,B_104,A_105] :
      ( r2_hidden(C_103,B_104)
      | ~ r2_hidden(C_103,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_446,plain,(
    ! [A_1,B_2,B_104] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_104)
      | ~ r1_tarski(A_1,B_104)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_439])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_481,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_497,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_481])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_529,plain,(
    ! [D_112] :
      ( ~ r2_hidden(D_112,'#skF_7')
      | ~ r2_hidden(D_112,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_10])).

tff(c_2289,plain,(
    ! [B_228] :
      ( ~ r2_hidden('#skF_1'(k3_subset_1('#skF_6','#skF_7'),B_228),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_228) ) ),
    inference(resolution,[status(thm)],[c_6,c_529])).

tff(c_2293,plain,(
    ! [B_2] :
      ( ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_2) ) ),
    inference(resolution,[status(thm)],[c_446,c_2289])).

tff(c_2304,plain,(
    ! [B_229] : r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_2293])).

tff(c_306,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,A_80)
      | ~ m1_subset_1(B_79,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_310,plain,(
    ! [B_79,A_16] :
      ( r1_tarski(B_79,A_16)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_306,c_34])).

tff(c_314,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_310])).

tff(c_327,plain,(
    ! [A_31] : r1_tarski(k1_xboole_0,A_31) ),
    inference(resolution,[status(thm)],[c_66,c_314])).

tff(c_368,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_377,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_327,c_368])).

tff(c_2325,plain,(
    k3_subset_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2304,c_377])).

tff(c_449,plain,(
    ! [A_106,B_107] :
      ( k3_subset_1(A_106,k3_subset_1(A_106,B_107)) = B_107
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_461,plain,(
    k3_subset_1('#skF_6',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_68,c_449])).

tff(c_2337,plain,(
    k3_subset_1('#skF_6',k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2325,c_461])).

tff(c_2342,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2337])).

tff(c_2344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_2342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.66  
% 3.71/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.71/1.66  
% 3.71/1.66  %Foreground sorts:
% 3.71/1.66  
% 3.71/1.66  
% 3.71/1.66  %Background operators:
% 3.71/1.66  
% 3.71/1.66  
% 3.71/1.66  %Foreground operators:
% 3.71/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.71/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.71/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.71/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.71/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.71/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.71/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.71/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.66  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.71/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.71/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.71/1.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.71/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.71/1.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.71/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.71/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.66  
% 4.12/1.67  tff(f_89, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.12/1.67  tff(f_81, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.12/1.67  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.12/1.67  tff(f_57, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.12/1.67  tff(f_72, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.12/1.67  tff(f_74, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.12/1.67  tff(f_87, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 4.12/1.67  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.12/1.67  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.12/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.12/1.67  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.12/1.67  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.12/1.67  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.12/1.67  tff(c_66, plain, (![A_31]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.12/1.67  tff(c_60, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.12/1.67  tff(c_142, plain, (![B_46, A_47]: (r2_hidden(B_46, A_47) | ~m1_subset_1(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.12/1.67  tff(c_34, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.67  tff(c_146, plain, (![B_46, A_16]: (r1_tarski(B_46, A_16) | ~m1_subset_1(B_46, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_142, c_34])).
% 4.12/1.67  tff(c_150, plain, (![B_48, A_49]: (r1_tarski(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(negUnitSimplification, [status(thm)], [c_60, c_146])).
% 4.12/1.67  tff(c_164, plain, (![A_31]: (r1_tarski(k1_xboole_0, A_31))), inference(resolution, [status(thm)], [c_66, c_150])).
% 4.12/1.67  tff(c_54, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.12/1.67  tff(c_56, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.12/1.67  tff(c_64, plain, (![A_30]: (k3_subset_1(A_30, k1_subset_1(A_30))=k2_subset_1(A_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.12/1.67  tff(c_78, plain, (![A_30]: (k3_subset_1(A_30, k1_subset_1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_64])).
% 4.12/1.67  tff(c_80, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_78])).
% 4.12/1.67  tff(c_277, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.12/1.67  tff(c_286, plain, (![A_31]: (k3_subset_1(A_31, k3_subset_1(A_31, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_277])).
% 4.12/1.67  tff(c_291, plain, (![A_31]: (k3_subset_1(A_31, A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_286])).
% 4.12/1.67  tff(c_70, plain, (k2_subset_1('#skF_6')!='#skF_7' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.12/1.67  tff(c_77, plain, ('#skF_7'!='#skF_6' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_70])).
% 4.12/1.67  tff(c_124, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_77])).
% 4.12/1.67  tff(c_76, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | k2_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.12/1.67  tff(c_79, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76])).
% 4.12/1.67  tff(c_125, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_124, c_79])).
% 4.12/1.67  tff(c_126, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_125, c_124])).
% 4.12/1.67  tff(c_292, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_126])).
% 4.12/1.67  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_292])).
% 4.12/1.67  tff(c_296, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_77])).
% 4.12/1.67  tff(c_297, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_77])).
% 4.12/1.67  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.12/1.67  tff(c_439, plain, (![C_103, B_104, A_105]: (r2_hidden(C_103, B_104) | ~r2_hidden(C_103, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.12/1.67  tff(c_446, plain, (![A_1, B_2, B_104]: (r2_hidden('#skF_1'(A_1, B_2), B_104) | ~r1_tarski(A_1, B_104) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_439])).
% 4.12/1.67  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.12/1.67  tff(c_481, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.12/1.67  tff(c_497, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_481])).
% 4.12/1.67  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.12/1.67  tff(c_529, plain, (![D_112]: (~r2_hidden(D_112, '#skF_7') | ~r2_hidden(D_112, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_497, c_10])).
% 4.12/1.67  tff(c_2289, plain, (![B_228]: (~r2_hidden('#skF_1'(k3_subset_1('#skF_6', '#skF_7'), B_228), '#skF_7') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_228))), inference(resolution, [status(thm)], [c_6, c_529])).
% 4.12/1.67  tff(c_2293, plain, (![B_2]: (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_2))), inference(resolution, [status(thm)], [c_446, c_2289])).
% 4.12/1.67  tff(c_2304, plain, (![B_229]: (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_229))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_2293])).
% 4.12/1.67  tff(c_306, plain, (![B_79, A_80]: (r2_hidden(B_79, A_80) | ~m1_subset_1(B_79, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.12/1.67  tff(c_310, plain, (![B_79, A_16]: (r1_tarski(B_79, A_16) | ~m1_subset_1(B_79, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_306, c_34])).
% 4.12/1.67  tff(c_314, plain, (![B_81, A_82]: (r1_tarski(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_60, c_310])).
% 4.12/1.67  tff(c_327, plain, (![A_31]: (r1_tarski(k1_xboole_0, A_31))), inference(resolution, [status(thm)], [c_66, c_314])).
% 4.12/1.67  tff(c_368, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.12/1.67  tff(c_377, plain, (![A_31]: (k1_xboole_0=A_31 | ~r1_tarski(A_31, k1_xboole_0))), inference(resolution, [status(thm)], [c_327, c_368])).
% 4.12/1.67  tff(c_2325, plain, (k3_subset_1('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_2304, c_377])).
% 4.12/1.67  tff(c_449, plain, (![A_106, B_107]: (k3_subset_1(A_106, k3_subset_1(A_106, B_107))=B_107 | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.12/1.67  tff(c_461, plain, (k3_subset_1('#skF_6', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_68, c_449])).
% 4.12/1.67  tff(c_2337, plain, (k3_subset_1('#skF_6', k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2325, c_461])).
% 4.12/1.67  tff(c_2342, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2337])).
% 4.12/1.67  tff(c_2344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_296, c_2342])).
% 4.12/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.67  
% 4.12/1.67  Inference rules
% 4.12/1.67  ----------------------
% 4.12/1.67  #Ref     : 0
% 4.12/1.67  #Sup     : 482
% 4.12/1.67  #Fact    : 0
% 4.12/1.67  #Define  : 0
% 4.12/1.67  #Split   : 8
% 4.12/1.67  #Chain   : 0
% 4.12/1.67  #Close   : 0
% 4.12/1.67  
% 4.12/1.67  Ordering : KBO
% 4.12/1.67  
% 4.12/1.67  Simplification rules
% 4.12/1.67  ----------------------
% 4.12/1.67  #Subsume      : 81
% 4.12/1.67  #Demod        : 125
% 4.12/1.67  #Tautology    : 154
% 4.12/1.67  #SimpNegUnit  : 49
% 4.12/1.67  #BackRed      : 28
% 4.12/1.67  
% 4.12/1.67  #Partial instantiations: 0
% 4.12/1.67  #Strategies tried      : 1
% 4.12/1.67  
% 4.12/1.67  Timing (in seconds)
% 4.12/1.67  ----------------------
% 4.12/1.68  Preprocessing        : 0.33
% 4.12/1.68  Parsing              : 0.17
% 4.12/1.68  CNF conversion       : 0.03
% 4.12/1.68  Main loop            : 0.57
% 4.12/1.68  Inferencing          : 0.19
% 4.12/1.68  Reduction            : 0.17
% 4.12/1.68  Demodulation         : 0.12
% 4.12/1.68  BG Simplification    : 0.03
% 4.12/1.68  Subsumption          : 0.13
% 4.12/1.68  Abstraction          : 0.03
% 4.12/1.68  MUC search           : 0.00
% 4.12/1.68  Cooper               : 0.00
% 4.12/1.68  Total                : 0.94
% 4.12/1.68  Index Insertion      : 0.00
% 4.12/1.68  Index Deletion       : 0.00
% 4.12/1.68  Index Matching       : 0.00
% 4.12/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
