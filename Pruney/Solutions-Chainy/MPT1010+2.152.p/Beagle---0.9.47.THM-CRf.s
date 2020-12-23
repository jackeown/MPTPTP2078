%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 161 expanded)
%              Number of leaves         :   34 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 334 expanded)
%              Number of equality atoms :   25 ( 125 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_94,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_102,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_100,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_98,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_96,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6618,plain,(
    ! [D_17386,C_17387,B_17388,A_17389] :
      ( r2_hidden(k1_funct_1(D_17386,C_17387),B_17388)
      | k1_xboole_0 = B_17388
      | ~ r2_hidden(C_17387,A_17389)
      | ~ m1_subset_1(D_17386,k1_zfmisc_1(k2_zfmisc_1(A_17389,B_17388)))
      | ~ v1_funct_2(D_17386,A_17389,B_17388)
      | ~ v1_funct_1(D_17386) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6742,plain,(
    ! [D_18442,B_18443] :
      ( r2_hidden(k1_funct_1(D_18442,'#skF_7'),B_18443)
      | k1_xboole_0 = B_18443
      | ~ m1_subset_1(D_18442,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_18443)))
      | ~ v1_funct_2(D_18442,'#skF_5',B_18443)
      | ~ v1_funct_1(D_18442) ) ),
    inference(resolution,[status(thm)],[c_96,c_6618])).

tff(c_6761,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_6742])).

tff(c_6768,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_6761])).

tff(c_6770,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6768])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6785,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6770,c_4])).

tff(c_30,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_175,plain,(
    ! [A_73,C_74,B_75] :
      ( r2_hidden(k2_mcart_1(A_73),C_74)
      | ~ r2_hidden(A_73,k2_zfmisc_1(k1_tarski(B_75),C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_180,plain,(
    ! [A_76] :
      ( r2_hidden(k2_mcart_1(A_76),k1_xboole_0)
      | ~ r2_hidden(A_76,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_175])).

tff(c_161,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_mcart_1(A_65) = B_66
      | ~ r2_hidden(A_65,k2_zfmisc_1(k1_tarski(B_66),C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_164,plain,(
    ! [A_65,B_66] :
      ( k1_mcart_1(A_65) = B_66
      | ~ r2_hidden(A_65,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_161])).

tff(c_204,plain,(
    ! [A_77] :
      ( k1_mcart_1(k2_mcart_1(A_77)) = '#skF_5'
      | ~ r2_hidden(A_77,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_180,c_164])).

tff(c_183,plain,(
    ! [A_76,B_66] :
      ( k1_mcart_1(k2_mcart_1(A_76)) = B_66
      | ~ r2_hidden(A_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_180,c_164])).

tff(c_207,plain,(
    ! [B_66,A_77] :
      ( B_66 = '#skF_5'
      | ~ r2_hidden(A_77,k1_xboole_0)
      | ~ r2_hidden(A_77,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_183])).

tff(c_487,plain,(
    ! [A_77] :
      ( ~ r2_hidden(A_77,k1_xboole_0)
      | ~ r2_hidden(A_77,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_6794,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6785,c_487])).

tff(c_6802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6785,c_6794])).

tff(c_6803,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_6768])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6809,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6803,c_2])).

tff(c_6814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6809])).

tff(c_6823,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_6815,plain,(
    ! [B_66] : B_66 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_6972,plain,(
    ! [B_22809] : B_22809 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6823,c_6815])).

tff(c_7050,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_6972,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.27  
% 6.16/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.27  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 6.16/2.27  
% 6.16/2.27  %Foreground sorts:
% 6.16/2.27  
% 6.16/2.27  
% 6.16/2.27  %Background operators:
% 6.16/2.27  
% 6.16/2.27  
% 6.16/2.27  %Foreground operators:
% 6.16/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.16/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.16/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.16/2.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.16/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.16/2.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.16/2.27  tff('#skF_7', type, '#skF_7': $i).
% 6.16/2.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.16/2.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.16/2.27  tff('#skF_5', type, '#skF_5': $i).
% 6.16/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.16/2.27  tff('#skF_6', type, '#skF_6': $i).
% 6.16/2.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.16/2.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.16/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.16/2.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.16/2.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.16/2.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.16/2.27  tff('#skF_8', type, '#skF_8': $i).
% 6.16/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.16/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.16/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.16/2.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.16/2.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.16/2.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.16/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.16/2.27  
% 6.16/2.28  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 6.16/2.28  tff(f_100, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 6.16/2.28  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.16/2.28  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.16/2.28  tff(f_88, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 6.16/2.28  tff(c_94, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.16/2.28  tff(c_102, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.16/2.28  tff(c_100, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.16/2.28  tff(c_98, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.16/2.28  tff(c_96, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.16/2.28  tff(c_6618, plain, (![D_17386, C_17387, B_17388, A_17389]: (r2_hidden(k1_funct_1(D_17386, C_17387), B_17388) | k1_xboole_0=B_17388 | ~r2_hidden(C_17387, A_17389) | ~m1_subset_1(D_17386, k1_zfmisc_1(k2_zfmisc_1(A_17389, B_17388))) | ~v1_funct_2(D_17386, A_17389, B_17388) | ~v1_funct_1(D_17386))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.16/2.28  tff(c_6742, plain, (![D_18442, B_18443]: (r2_hidden(k1_funct_1(D_18442, '#skF_7'), B_18443) | k1_xboole_0=B_18443 | ~m1_subset_1(D_18442, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_18443))) | ~v1_funct_2(D_18442, '#skF_5', B_18443) | ~v1_funct_1(D_18442))), inference(resolution, [status(thm)], [c_96, c_6618])).
% 6.16/2.28  tff(c_6761, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_98, c_6742])).
% 6.16/2.28  tff(c_6768, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_6761])).
% 6.16/2.28  tff(c_6770, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6768])).
% 6.16/2.28  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.28  tff(c_6785, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6770, c_4])).
% 6.16/2.28  tff(c_30, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.16/2.28  tff(c_175, plain, (![A_73, C_74, B_75]: (r2_hidden(k2_mcart_1(A_73), C_74) | ~r2_hidden(A_73, k2_zfmisc_1(k1_tarski(B_75), C_74)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.16/2.28  tff(c_180, plain, (![A_76]: (r2_hidden(k2_mcart_1(A_76), k1_xboole_0) | ~r2_hidden(A_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_175])).
% 6.16/2.28  tff(c_161, plain, (![A_65, B_66, C_67]: (k1_mcart_1(A_65)=B_66 | ~r2_hidden(A_65, k2_zfmisc_1(k1_tarski(B_66), C_67)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.16/2.28  tff(c_164, plain, (![A_65, B_66]: (k1_mcart_1(A_65)=B_66 | ~r2_hidden(A_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_161])).
% 6.16/2.28  tff(c_204, plain, (![A_77]: (k1_mcart_1(k2_mcart_1(A_77))='#skF_5' | ~r2_hidden(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_164])).
% 6.16/2.28  tff(c_183, plain, (![A_76, B_66]: (k1_mcart_1(k2_mcart_1(A_76))=B_66 | ~r2_hidden(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_164])).
% 6.16/2.28  tff(c_207, plain, (![B_66, A_77]: (B_66='#skF_5' | ~r2_hidden(A_77, k1_xboole_0) | ~r2_hidden(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_204, c_183])).
% 6.16/2.28  tff(c_487, plain, (![A_77]: (~r2_hidden(A_77, k1_xboole_0) | ~r2_hidden(A_77, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_207])).
% 6.16/2.28  tff(c_6794, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_6785, c_487])).
% 6.16/2.28  tff(c_6802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6785, c_6794])).
% 6.16/2.28  tff(c_6803, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_6768])).
% 6.16/2.28  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.28  tff(c_6809, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_6803, c_2])).
% 6.16/2.28  tff(c_6814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_6809])).
% 6.16/2.28  tff(c_6823, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_207])).
% 6.16/2.28  tff(c_6815, plain, (![B_66]: (B_66='#skF_5')), inference(splitRight, [status(thm)], [c_207])).
% 6.16/2.28  tff(c_6972, plain, (![B_22809]: (B_22809='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6823, c_6815])).
% 6.16/2.28  tff(c_7050, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_6972, c_94])).
% 6.16/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.28  
% 6.16/2.28  Inference rules
% 6.16/2.28  ----------------------
% 6.16/2.28  #Ref     : 0
% 6.16/2.28  #Sup     : 1429
% 6.16/2.28  #Fact    : 0
% 6.16/2.28  #Define  : 0
% 6.16/2.28  #Split   : 10
% 6.16/2.28  #Chain   : 0
% 6.16/2.28  #Close   : 0
% 6.16/2.28  
% 6.16/2.28  Ordering : KBO
% 6.16/2.28  
% 6.16/2.28  Simplification rules
% 6.16/2.28  ----------------------
% 6.16/2.28  #Subsume      : 738
% 6.16/2.28  #Demod        : 70
% 6.16/2.28  #Tautology    : 102
% 6.16/2.28  #SimpNegUnit  : 18
% 6.16/2.28  #BackRed      : 8
% 6.16/2.28  
% 6.16/2.28  #Partial instantiations: 6625
% 6.16/2.28  #Strategies tried      : 1
% 6.16/2.28  
% 6.16/2.28  Timing (in seconds)
% 6.16/2.28  ----------------------
% 6.16/2.29  Preprocessing        : 0.41
% 6.16/2.29  Parsing              : 0.19
% 6.16/2.29  CNF conversion       : 0.03
% 6.16/2.29  Main loop            : 1.07
% 6.16/2.29  Inferencing          : 0.46
% 6.16/2.29  Reduction            : 0.29
% 6.16/2.29  Demodulation         : 0.21
% 6.16/2.29  BG Simplification    : 0.05
% 6.16/2.29  Subsumption          : 0.21
% 6.16/2.29  Abstraction          : 0.06
% 6.16/2.29  MUC search           : 0.00
% 6.16/2.29  Cooper               : 0.00
% 6.16/2.29  Total                : 1.50
% 6.16/2.29  Index Insertion      : 0.00
% 6.16/2.29  Index Deletion       : 0.00
% 6.16/2.29  Index Matching       : 0.00
% 6.16/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
