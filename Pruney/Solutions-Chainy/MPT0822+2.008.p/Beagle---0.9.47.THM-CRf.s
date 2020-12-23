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
% DateTime   : Thu Dec  3 10:07:11 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
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
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_11 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

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
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_534,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relset_1(A_149,B_150,C_151) = k2_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_538,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_534])).

tff(c_52,plain,
    ( k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9'
    | r2_hidden('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_539,plain,(
    k2_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [D_47] :
      ( r2_hidden(k4_tarski('#skF_11'(D_47),D_47),'#skF_10')
      | ~ r2_hidden(D_47,'#skF_9')
      | k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_501,plain,(
    ! [D_143] :
      ( r2_hidden(k4_tarski('#skF_11'(D_143),D_143),'#skF_10')
      | ~ r2_hidden(D_143,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58])).

tff(c_32,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k2_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(D_34,C_31),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_509,plain,(
    ! [D_144] :
      ( r2_hidden(D_144,k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_144,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_501,c_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_564,plain,(
    ! [A_161] :
      ( r1_tarski(A_161,k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_1'(A_161,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_509,c_4])).

tff(c_572,plain,(
    r1_tarski('#skF_9',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6,c_564])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_575,plain,
    ( k2_relat_1('#skF_10') = '#skF_9'
    | ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_572,c_8])).

tff(c_578,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_575])).

tff(c_579,plain,(
    ! [A_162,B_163,C_164] :
      ( m1_subset_1(k2_relset_1(A_162,B_163,C_164),k1_zfmisc_1(B_163))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_589,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_579])).

tff(c_593,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9')) ),
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
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_593,c_76])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_596])).

tff(c_601,plain,(
    r2_hidden('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_602,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_715,plain,(
    ! [A_189,B_190,C_191] :
      ( k2_relset_1(A_189,B_190,C_191) = k2_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_718,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_46,c_715])).

tff(c_720,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_718])).

tff(c_882,plain,(
    ! [A_236,C_237] :
      ( r2_hidden(k4_tarski('#skF_7'(A_236,k2_relat_1(A_236),C_237),C_237),A_236)
      | ~ r2_hidden(C_237,k2_relat_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [E_50] :
      ( k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9'
      | ~ r2_hidden(k4_tarski(E_50,'#skF_12'),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_603,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_603])).

tff(c_610,plain,(
    ! [E_50] : ~ r2_hidden(k4_tarski(E_50,'#skF_12'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_891,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_882,c_610])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_720,c_891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:09:29 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_11 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.83/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.83/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.43  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.83/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_11', type, '#skF_11': $i > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.83/1.43  tff('#skF_12', type, '#skF_12': $i).
% 2.83/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.83/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.43  
% 2.83/1.45  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.83/1.45  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.83/1.45  tff(f_62, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.83/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.45  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.83/1.45  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.83/1.45  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.83/1.45  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.83/1.45  tff(c_46, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.45  tff(c_534, plain, (![A_149, B_150, C_151]: (k2_relset_1(A_149, B_150, C_151)=k2_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.83/1.45  tff(c_538, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_46, c_534])).
% 2.83/1.45  tff(c_52, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9' | r2_hidden('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.45  tff(c_68, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 2.83/1.45  tff(c_539, plain, (k2_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_68])).
% 2.83/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.45  tff(c_58, plain, (![D_47]: (r2_hidden(k4_tarski('#skF_11'(D_47), D_47), '#skF_10') | ~r2_hidden(D_47, '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.45  tff(c_501, plain, (![D_143]: (r2_hidden(k4_tarski('#skF_11'(D_143), D_143), '#skF_10') | ~r2_hidden(D_143, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_68, c_58])).
% 2.83/1.45  tff(c_32, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k2_relat_1(A_16)) | ~r2_hidden(k4_tarski(D_34, C_31), A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_509, plain, (![D_144]: (r2_hidden(D_144, k2_relat_1('#skF_10')) | ~r2_hidden(D_144, '#skF_9'))), inference(resolution, [status(thm)], [c_501, c_32])).
% 2.83/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.45  tff(c_564, plain, (![A_161]: (r1_tarski(A_161, k2_relat_1('#skF_10')) | ~r2_hidden('#skF_1'(A_161, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_509, c_4])).
% 2.83/1.45  tff(c_572, plain, (r1_tarski('#skF_9', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6, c_564])).
% 2.83/1.45  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.45  tff(c_575, plain, (k2_relat_1('#skF_10')='#skF_9' | ~r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_572, c_8])).
% 2.83/1.45  tff(c_578, plain, (~r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_539, c_575])).
% 2.83/1.45  tff(c_579, plain, (![A_162, B_163, C_164]: (m1_subset_1(k2_relset_1(A_162, B_163, C_164), k1_zfmisc_1(B_163)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.45  tff(c_589, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_538, c_579])).
% 2.83/1.45  tff(c_593, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_589])).
% 2.83/1.45  tff(c_26, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.83/1.45  tff(c_69, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | v1_xboole_0(B_58) | ~m1_subset_1(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.45  tff(c_14, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.45  tff(c_73, plain, (![A_57, A_8]: (r1_tarski(A_57, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_57, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_69, c_14])).
% 2.83/1.45  tff(c_76, plain, (![A_57, A_8]: (r1_tarski(A_57, A_8) | ~m1_subset_1(A_57, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_26, c_73])).
% 2.83/1.45  tff(c_596, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_593, c_76])).
% 2.83/1.45  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_578, c_596])).
% 2.83/1.45  tff(c_601, plain, (r2_hidden('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 2.83/1.45  tff(c_602, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 2.83/1.45  tff(c_715, plain, (![A_189, B_190, C_191]: (k2_relset_1(A_189, B_190, C_191)=k2_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.83/1.45  tff(c_718, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_46, c_715])).
% 2.83/1.45  tff(c_720, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_718])).
% 2.83/1.45  tff(c_882, plain, (![A_236, C_237]: (r2_hidden(k4_tarski('#skF_7'(A_236, k2_relat_1(A_236), C_237), C_237), A_236) | ~r2_hidden(C_237, k2_relat_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_48, plain, (![E_50]: (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9' | ~r2_hidden(k4_tarski(E_50, '#skF_12'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.45  tff(c_603, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_48])).
% 2.83/1.45  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_602, c_603])).
% 2.83/1.45  tff(c_610, plain, (![E_50]: (~r2_hidden(k4_tarski(E_50, '#skF_12'), '#skF_10'))), inference(splitRight, [status(thm)], [c_48])).
% 2.83/1.45  tff(c_891, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_882, c_610])).
% 2.83/1.45  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_601, c_720, c_891])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 0
% 2.83/1.45  #Sup     : 177
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 12
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 15
% 2.83/1.45  #Demod        : 33
% 2.83/1.45  #Tautology    : 34
% 2.83/1.45  #SimpNegUnit  : 9
% 2.83/1.45  #BackRed      : 2
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 3.07/1.45  Preprocessing        : 0.30
% 3.07/1.45  Parsing              : 0.15
% 3.07/1.45  CNF conversion       : 0.02
% 3.07/1.45  Main loop            : 0.38
% 3.07/1.45  Inferencing          : 0.14
% 3.07/1.45  Reduction            : 0.10
% 3.07/1.45  Demodulation         : 0.07
% 3.07/1.45  BG Simplification    : 0.02
% 3.07/1.45  Subsumption          : 0.08
% 3.07/1.45  Abstraction          : 0.02
% 3.07/1.45  MUC search           : 0.00
% 3.07/1.45  Cooper               : 0.00
% 3.07/1.45  Total                : 0.71
% 3.07/1.45  Index Insertion      : 0.00
% 3.07/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
