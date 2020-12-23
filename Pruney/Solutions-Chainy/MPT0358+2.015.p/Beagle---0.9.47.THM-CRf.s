%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 119 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 166 expanded)
%              Number of equality atoms :   30 (  65 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_30] : k1_subset_1(A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_75,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_74])).

tff(c_131,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_38,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_132,plain,(
    ! [A_22] : r1_xboole_0(A_22,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_38])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_155,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = '#skF_7'
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_28])).

tff(c_163,plain,(
    ! [A_22] : k3_xboole_0(A_22,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_132,c_155])).

tff(c_36,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_447,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,A_74)
      | ~ r2_hidden(D_73,k4_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_771,plain,(
    ! [D_104,A_105,B_106] :
      ( r2_hidden(D_104,A_105)
      | ~ r2_hidden(D_104,k3_xboole_0(A_105,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_447])).

tff(c_797,plain,(
    ! [D_107,A_108] :
      ( r2_hidden(D_107,A_108)
      | ~ r2_hidden(D_107,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_771])).

tff(c_898,plain,(
    ! [B_115,A_116] :
      ( r2_hidden('#skF_1'('#skF_7',B_115),A_116)
      | r1_tarski('#skF_7',B_115) ) ),
    inference(resolution,[status(thm)],[c_8,c_797])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_953,plain,(
    ! [A_116] : r1_tarski('#skF_7',A_116) ),
    inference(resolution,[status(thm)],[c_898,c_6])).

tff(c_68,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_76,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_130])).

tff(c_962,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_130])).

tff(c_966,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_967,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_974,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = A_121
      | ~ r1_tarski(A_121,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_978,plain,(
    k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_967,c_974])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1052,plain,(
    ! [A_130,B_131] : k4_xboole_0(A_130,k4_xboole_0(A_130,B_131)) = k3_xboole_0(A_130,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1601,plain,(
    ! [D_172,A_173,B_174] :
      ( r2_hidden(D_172,A_173)
      | ~ r2_hidden(D_172,k3_xboole_0(A_173,B_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_14])).

tff(c_1659,plain,(
    ! [D_179,B_180,A_181] :
      ( r2_hidden(D_179,B_180)
      | ~ r2_hidden(D_179,k3_xboole_0(A_181,B_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1601])).

tff(c_1813,plain,(
    ! [D_188] :
      ( r2_hidden(D_188,k3_subset_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_188,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_1659])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1392,plain,(
    ! [A_158,B_159] :
      ( k4_xboole_0(A_158,B_159) = k3_subset_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1405,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_1392])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1409,plain,(
    ! [D_13] :
      ( ~ r2_hidden(D_13,'#skF_7')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1405,c_12])).

tff(c_1842,plain,(
    ! [D_189] : ~ r2_hidden(D_189,'#skF_7') ),
    inference(resolution,[status(thm)],[c_1813,c_1409])).

tff(c_1879,plain,(
    ! [B_191] : r1_tarski('#skF_7',B_191) ),
    inference(resolution,[status(thm)],[c_8,c_1842])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1886,plain,(
    ! [B_192] : k3_xboole_0('#skF_7',B_192) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1879,c_34])).

tff(c_983,plain,(
    ! [A_123,B_124] :
      ( k3_xboole_0(A_123,B_124) = k1_xboole_0
      | ~ r1_xboole_0(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_991,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_983])).

tff(c_1907,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1886,c_991])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_966,c_1907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:22:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.59  
% 3.33/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.33/1.60  
% 3.33/1.60  %Foreground sorts:
% 3.33/1.60  
% 3.33/1.60  
% 3.33/1.60  %Background operators:
% 3.33/1.60  
% 3.33/1.60  
% 3.33/1.60  %Foreground operators:
% 3.33/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.33/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.33/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.33/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.33/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.60  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.33/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.33/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.33/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.60  
% 3.33/1.61  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.33/1.61  tff(f_80, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.33/1.61  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.33/1.61  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.33/1.61  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.33/1.61  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.33/1.61  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.33/1.61  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.33/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.33/1.61  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.33/1.61  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.61  tff(c_60, plain, (![A_30]: (k1_subset_1(A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.33/1.61  tff(c_74, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.33/1.61  tff(c_75, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_74])).
% 3.33/1.61  tff(c_131, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_75])).
% 3.33/1.61  tff(c_38, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.33/1.61  tff(c_132, plain, (![A_22]: (r1_xboole_0(A_22, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_38])).
% 3.33/1.61  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.61  tff(c_155, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)='#skF_7' | ~r1_xboole_0(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_28])).
% 3.33/1.61  tff(c_163, plain, (![A_22]: (k3_xboole_0(A_22, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_132, c_155])).
% 3.33/1.61  tff(c_36, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.61  tff(c_447, plain, (![D_73, A_74, B_75]: (r2_hidden(D_73, A_74) | ~r2_hidden(D_73, k4_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.61  tff(c_771, plain, (![D_104, A_105, B_106]: (r2_hidden(D_104, A_105) | ~r2_hidden(D_104, k3_xboole_0(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_447])).
% 3.33/1.61  tff(c_797, plain, (![D_107, A_108]: (r2_hidden(D_107, A_108) | ~r2_hidden(D_107, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_771])).
% 3.33/1.61  tff(c_898, plain, (![B_115, A_116]: (r2_hidden('#skF_1'('#skF_7', B_115), A_116) | r1_tarski('#skF_7', B_115))), inference(resolution, [status(thm)], [c_8, c_797])).
% 3.33/1.61  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.61  tff(c_953, plain, (![A_116]: (r1_tarski('#skF_7', A_116))), inference(resolution, [status(thm)], [c_898, c_6])).
% 3.33/1.61  tff(c_68, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.33/1.61  tff(c_76, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68])).
% 3.33/1.61  tff(c_130, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_76])).
% 3.33/1.61  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_953, c_130])).
% 3.33/1.61  tff(c_962, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_75])).
% 3.33/1.61  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_962, c_130])).
% 3.33/1.61  tff(c_966, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 3.33/1.61  tff(c_967, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_76])).
% 3.33/1.61  tff(c_974, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=A_121 | ~r1_tarski(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.61  tff(c_978, plain, (k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_967, c_974])).
% 3.33/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.61  tff(c_1052, plain, (![A_130, B_131]: (k4_xboole_0(A_130, k4_xboole_0(A_130, B_131))=k3_xboole_0(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.61  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.61  tff(c_1601, plain, (![D_172, A_173, B_174]: (r2_hidden(D_172, A_173) | ~r2_hidden(D_172, k3_xboole_0(A_173, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_1052, c_14])).
% 3.33/1.61  tff(c_1659, plain, (![D_179, B_180, A_181]: (r2_hidden(D_179, B_180) | ~r2_hidden(D_179, k3_xboole_0(A_181, B_180)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1601])).
% 3.33/1.61  tff(c_1813, plain, (![D_188]: (r2_hidden(D_188, k3_subset_1('#skF_6', '#skF_7')) | ~r2_hidden(D_188, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_978, c_1659])).
% 3.33/1.61  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.33/1.61  tff(c_1392, plain, (![A_158, B_159]: (k4_xboole_0(A_158, B_159)=k3_subset_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.33/1.61  tff(c_1405, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_66, c_1392])).
% 3.33/1.61  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.61  tff(c_1409, plain, (![D_13]: (~r2_hidden(D_13, '#skF_7') | ~r2_hidden(D_13, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1405, c_12])).
% 3.33/1.61  tff(c_1842, plain, (![D_189]: (~r2_hidden(D_189, '#skF_7'))), inference(resolution, [status(thm)], [c_1813, c_1409])).
% 3.33/1.61  tff(c_1879, plain, (![B_191]: (r1_tarski('#skF_7', B_191))), inference(resolution, [status(thm)], [c_8, c_1842])).
% 3.33/1.61  tff(c_34, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.61  tff(c_1886, plain, (![B_192]: (k3_xboole_0('#skF_7', B_192)='#skF_7')), inference(resolution, [status(thm)], [c_1879, c_34])).
% 3.33/1.61  tff(c_983, plain, (![A_123, B_124]: (k3_xboole_0(A_123, B_124)=k1_xboole_0 | ~r1_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.61  tff(c_991, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_983])).
% 3.33/1.61  tff(c_1907, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1886, c_991])).
% 3.33/1.61  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_966, c_1907])).
% 3.33/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.61  
% 3.33/1.61  Inference rules
% 3.33/1.61  ----------------------
% 3.33/1.61  #Ref     : 0
% 3.33/1.61  #Sup     : 460
% 3.33/1.61  #Fact    : 0
% 3.33/1.61  #Define  : 0
% 3.33/1.61  #Split   : 3
% 3.33/1.61  #Chain   : 0
% 3.33/1.61  #Close   : 0
% 3.33/1.61  
% 3.33/1.61  Ordering : KBO
% 3.33/1.61  
% 3.33/1.61  Simplification rules
% 3.33/1.61  ----------------------
% 3.33/1.61  #Subsume      : 58
% 3.33/1.61  #Demod        : 156
% 3.33/1.61  #Tautology    : 219
% 3.33/1.61  #SimpNegUnit  : 8
% 3.33/1.61  #BackRed      : 6
% 3.33/1.61  
% 3.33/1.61  #Partial instantiations: 0
% 3.33/1.61  #Strategies tried      : 1
% 3.33/1.61  
% 3.33/1.61  Timing (in seconds)
% 3.33/1.61  ----------------------
% 3.33/1.61  Preprocessing        : 0.33
% 3.33/1.61  Parsing              : 0.17
% 3.33/1.61  CNF conversion       : 0.02
% 3.33/1.61  Main loop            : 0.51
% 3.33/1.61  Inferencing          : 0.18
% 3.33/1.61  Reduction            : 0.17
% 3.33/1.61  Demodulation         : 0.12
% 3.33/1.61  BG Simplification    : 0.03
% 3.33/1.62  Subsumption          : 0.09
% 3.33/1.62  Abstraction          : 0.03
% 3.33/1.62  MUC search           : 0.00
% 3.33/1.62  Cooper               : 0.00
% 3.33/1.62  Total                : 0.88
% 3.33/1.62  Index Insertion      : 0.00
% 3.33/1.62  Index Deletion       : 0.00
% 3.33/1.62  Index Matching       : 0.00
% 3.33/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
