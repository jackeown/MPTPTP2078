%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:09 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 159 expanded)
%              Number of equality atoms :   19 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_11 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_534,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_538,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_534])).

tff(c_52,plain,
    ( k1_relset_1('#skF_9','#skF_8','#skF_10') != '#skF_9'
    | r2_hidden('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_539,plain,(
    k1_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [D_47] :
      ( r2_hidden(k4_tarski(D_47,'#skF_11'(D_47)),'#skF_10')
      | ~ r2_hidden(D_47,'#skF_9')
      | k1_relset_1('#skF_9','#skF_8','#skF_10') = '#skF_9' ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_501,plain,(
    ! [D_143] :
      ( r2_hidden(k4_tarski(D_143,'#skF_11'(D_143)),'#skF_10')
      | ~ r2_hidden(D_143,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58])).

tff(c_32,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_509,plain,(
    ! [D_144] :
      ( r2_hidden(D_144,k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_144,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_501,c_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_564,plain,(
    ! [A_161] :
      ( r1_tarski(A_161,k1_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_1'(A_161,k1_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_509,c_4])).

tff(c_572,plain,(
    r1_tarski('#skF_9',k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6,c_564])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_575,plain,
    ( k1_relat_1('#skF_10') = '#skF_9'
    | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_572,c_8])).

tff(c_578,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_575])).

tff(c_579,plain,(
    ! [A_162,B_163,C_164] :
      ( m1_subset_1(k1_relset_1(A_162,B_163,C_164),k1_zfmisc_1(A_162))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_589,plain,
    ( m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_579])).

tff(c_593,plain,(
    m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_589])).

tff(c_26,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [A_57,A_8] :
      ( r1_tarski(A_57,A_8)
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_57,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_69,c_14])).

tff(c_76,plain,(
    ! [A_57,A_8] :
      ( r1_tarski(A_57,A_8)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_73])).

tff(c_596,plain,(
    r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_593,c_76])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_596])).

tff(c_601,plain,(
    r2_hidden('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_602,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_715,plain,(
    ! [A_189,B_190,C_191] :
      ( k1_relset_1(A_189,B_190,C_191) = k1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_718,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_715])).

tff(c_720,plain,(
    k1_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_718])).

tff(c_882,plain,(
    ! [C_236,A_237] :
      ( r2_hidden(k4_tarski(C_236,'#skF_7'(A_237,k1_relat_1(A_237),C_236)),A_237)
      | ~ r2_hidden(C_236,k1_relat_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [E_50] :
      ( k1_relset_1('#skF_9','#skF_8','#skF_10') != '#skF_9'
      | ~ r2_hidden(k4_tarski('#skF_12',E_50),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_603,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_603])).

tff(c_610,plain,(
    ! [E_50] : ~ r2_hidden(k4_tarski('#skF_12',E_50),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_891,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_882,c_610])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_720,c_891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.55  
% 3.14/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_11 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 3.14/1.55  
% 3.14/1.55  %Foreground sorts:
% 3.14/1.55  
% 3.14/1.55  
% 3.14/1.55  %Background operators:
% 3.14/1.55  
% 3.14/1.55  
% 3.14/1.55  %Foreground operators:
% 3.14/1.55  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.14/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.55  tff('#skF_10', type, '#skF_10': $i).
% 3.14/1.55  tff('#skF_9', type, '#skF_9': $i).
% 3.14/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.55  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.14/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.55  tff('#skF_11', type, '#skF_11': $i > $i).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.14/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.55  tff('#skF_12', type, '#skF_12': $i).
% 3.14/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.14/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.55  
% 3.14/1.56  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.14/1.56  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.14/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.14/1.56  tff(f_62, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.14/1.56  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.56  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.14/1.56  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.14/1.56  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.14/1.56  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.14/1.56  tff(c_46, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.56  tff(c_534, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.14/1.56  tff(c_538, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_46, c_534])).
% 3.14/1.56  tff(c_52, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')!='#skF_9' | r2_hidden('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.56  tff(c_68, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 3.14/1.56  tff(c_539, plain, (k1_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_68])).
% 3.14/1.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.56  tff(c_58, plain, (![D_47]: (r2_hidden(k4_tarski(D_47, '#skF_11'(D_47)), '#skF_10') | ~r2_hidden(D_47, '#skF_9') | k1_relset_1('#skF_9', '#skF_8', '#skF_10')='#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.56  tff(c_501, plain, (![D_143]: (r2_hidden(k4_tarski(D_143, '#skF_11'(D_143)), '#skF_10') | ~r2_hidden(D_143, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_68, c_58])).
% 3.14/1.56  tff(c_32, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.56  tff(c_509, plain, (![D_144]: (r2_hidden(D_144, k1_relat_1('#skF_10')) | ~r2_hidden(D_144, '#skF_9'))), inference(resolution, [status(thm)], [c_501, c_32])).
% 3.14/1.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.56  tff(c_564, plain, (![A_161]: (r1_tarski(A_161, k1_relat_1('#skF_10')) | ~r2_hidden('#skF_1'(A_161, k1_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_509, c_4])).
% 3.14/1.56  tff(c_572, plain, (r1_tarski('#skF_9', k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6, c_564])).
% 3.14/1.56  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.56  tff(c_575, plain, (k1_relat_1('#skF_10')='#skF_9' | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_572, c_8])).
% 3.14/1.56  tff(c_578, plain, (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_539, c_575])).
% 3.14/1.56  tff(c_579, plain, (![A_162, B_163, C_164]: (m1_subset_1(k1_relset_1(A_162, B_163, C_164), k1_zfmisc_1(A_162)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.56  tff(c_589, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_538, c_579])).
% 3.14/1.56  tff(c_593, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_589])).
% 3.14/1.56  tff(c_26, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.56  tff(c_69, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | v1_xboole_0(B_58) | ~m1_subset_1(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.56  tff(c_14, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.56  tff(c_73, plain, (![A_57, A_8]: (r1_tarski(A_57, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_57, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_69, c_14])).
% 3.14/1.56  tff(c_76, plain, (![A_57, A_8]: (r1_tarski(A_57, A_8) | ~m1_subset_1(A_57, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_26, c_73])).
% 3.14/1.56  tff(c_596, plain, (r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_593, c_76])).
% 3.14/1.56  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_578, c_596])).
% 3.14/1.56  tff(c_601, plain, (r2_hidden('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 3.14/1.56  tff(c_602, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 3.14/1.56  tff(c_715, plain, (![A_189, B_190, C_191]: (k1_relset_1(A_189, B_190, C_191)=k1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.14/1.56  tff(c_718, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_46, c_715])).
% 3.14/1.56  tff(c_720, plain, (k1_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_718])).
% 3.14/1.56  tff(c_882, plain, (![C_236, A_237]: (r2_hidden(k4_tarski(C_236, '#skF_7'(A_237, k1_relat_1(A_237), C_236)), A_237) | ~r2_hidden(C_236, k1_relat_1(A_237)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.56  tff(c_48, plain, (![E_50]: (k1_relset_1('#skF_9', '#skF_8', '#skF_10')!='#skF_9' | ~r2_hidden(k4_tarski('#skF_12', E_50), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.56  tff(c_603, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_48])).
% 3.14/1.56  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_602, c_603])).
% 3.14/1.56  tff(c_610, plain, (![E_50]: (~r2_hidden(k4_tarski('#skF_12', E_50), '#skF_10'))), inference(splitRight, [status(thm)], [c_48])).
% 3.14/1.56  tff(c_891, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_882, c_610])).
% 3.14/1.56  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_601, c_720, c_891])).
% 3.14/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.56  
% 3.14/1.56  Inference rules
% 3.14/1.56  ----------------------
% 3.14/1.56  #Ref     : 0
% 3.14/1.56  #Sup     : 177
% 3.14/1.56  #Fact    : 0
% 3.14/1.56  #Define  : 0
% 3.14/1.56  #Split   : 12
% 3.14/1.56  #Chain   : 0
% 3.14/1.56  #Close   : 0
% 3.14/1.56  
% 3.14/1.56  Ordering : KBO
% 3.14/1.56  
% 3.14/1.56  Simplification rules
% 3.14/1.56  ----------------------
% 3.14/1.56  #Subsume      : 15
% 3.14/1.56  #Demod        : 33
% 3.14/1.56  #Tautology    : 34
% 3.14/1.56  #SimpNegUnit  : 9
% 3.14/1.56  #BackRed      : 2
% 3.14/1.56  
% 3.14/1.56  #Partial instantiations: 0
% 3.14/1.56  #Strategies tried      : 1
% 3.14/1.56  
% 3.14/1.56  Timing (in seconds)
% 3.14/1.56  ----------------------
% 3.14/1.57  Preprocessing        : 0.34
% 3.14/1.57  Parsing              : 0.17
% 3.14/1.57  CNF conversion       : 0.03
% 3.14/1.57  Main loop            : 0.38
% 3.14/1.57  Inferencing          : 0.15
% 3.14/1.57  Reduction            : 0.10
% 3.14/1.57  Demodulation         : 0.07
% 3.14/1.57  BG Simplification    : 0.02
% 3.14/1.57  Subsumption          : 0.08
% 3.14/1.57  Abstraction          : 0.02
% 3.14/1.57  MUC search           : 0.00
% 3.14/1.57  Cooper               : 0.00
% 3.14/1.57  Total                : 0.75
% 3.14/1.57  Index Insertion      : 0.00
% 3.14/1.57  Index Deletion       : 0.00
% 3.14/1.57  Index Matching       : 0.00
% 3.14/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
