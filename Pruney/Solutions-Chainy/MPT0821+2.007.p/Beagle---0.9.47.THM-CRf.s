%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:09 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 106 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 173 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_12 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_308,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_312,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_48,c_308])).

tff(c_54,plain,
    ( k1_relset_1('#skF_10','#skF_9','#skF_11') != '#skF_10'
    | r2_hidden('#skF_13','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_102,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_313,plain,(
    k1_relat_1('#skF_11') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_102])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [D_50] :
      ( r2_hidden(k4_tarski(D_50,'#skF_12'(D_50)),'#skF_11')
      | ~ r2_hidden(D_50,'#skF_10')
      | k1_relset_1('#skF_10','#skF_9','#skF_11') = '#skF_10' ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_246,plain,(
    ! [D_94] :
      ( r2_hidden(k4_tarski(D_94,'#skF_12'(D_94)),'#skF_11')
      | ~ r2_hidden(D_94,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_60])).

tff(c_34,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k1_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(C_34,D_37),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_290,plain,(
    ! [D_97] :
      ( r2_hidden(D_97,k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_97,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_246,c_34])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_634,plain,(
    ! [A_146] :
      ( r1_tarski(A_146,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_2'(A_146,k1_relat_1('#skF_11')),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_290,c_8])).

tff(c_642,plain,(
    r1_tarski('#skF_10',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_10,c_634])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_667,plain,
    ( k1_relat_1('#skF_11') = '#skF_10'
    | ~ r1_tarski(k1_relat_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_642,c_12])).

tff(c_678,plain,(
    ~ r1_tarski(k1_relat_1('#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_667])).

tff(c_1275,plain,(
    ! [A_200,B_201,C_202] :
      ( m1_subset_1(k1_relset_1(A_200,B_201,C_202),k1_zfmisc_1(A_200))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1285,plain,
    ( m1_subset_1(k1_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_1275])).

tff(c_1289,plain,(
    m1_subset_1(k1_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1285])).

tff(c_85,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | v1_xboole_0(B_65)
      | ~ m1_subset_1(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    ! [A_64,A_12] :
      ( r1_tarski(A_64,A_12)
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ m1_subset_1(A_64,k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_85,c_18])).

tff(c_1292,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),'#skF_10')
    | v1_xboole_0(k1_zfmisc_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1289,c_93])).

tff(c_1295,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_1292])).

tff(c_69,plain,(
    ! [C_58,A_59] :
      ( r2_hidden(C_58,k1_zfmisc_1(A_59))
      | ~ r1_tarski(C_58,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_59,C_58] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_59))
      | ~ r1_tarski(C_58,A_59) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_1302,plain,(
    ! [C_203] : ~ r1_tarski(C_203,'#skF_10') ),
    inference(resolution,[status(thm)],[c_1295,c_73])).

tff(c_1343,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_1302])).

tff(c_1344,plain,(
    r2_hidden('#skF_13','#skF_10') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1345,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,(
    ! [E_53] :
      ( k1_relset_1('#skF_10','#skF_9','#skF_11') != '#skF_10'
      | ~ r2_hidden(k4_tarski('#skF_13',E_53),'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1346,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1346])).

tff(c_1358,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1496,plain,(
    ! [A_228,B_229,C_230] :
      ( k1_relset_1(A_228,B_229,C_230) = k1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1499,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_48,c_1496])).

tff(c_1501,plain,(
    k1_relat_1('#skF_11') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_1499])).

tff(c_1772,plain,(
    ! [C_270,A_271] :
      ( r2_hidden(k4_tarski(C_270,'#skF_8'(A_271,k1_relat_1(A_271),C_270)),A_271)
      | ~ r2_hidden(C_270,k1_relat_1(A_271)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1357,plain,(
    ! [E_53] : ~ r2_hidden(k4_tarski('#skF_13',E_53),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1781,plain,(
    ~ r2_hidden('#skF_13',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_1772,c_1357])).

tff(c_1797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_1501,c_1781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:02:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.59  
% 3.59/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.59  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_12 > #skF_7 > #skF_5 > #skF_4
% 3.59/1.59  
% 3.59/1.59  %Foreground sorts:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Background operators:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Foreground operators:
% 3.59/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.59  tff('#skF_11', type, '#skF_11': $i).
% 3.59/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.59/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.59/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.59/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.59  tff('#skF_10', type, '#skF_10': $i).
% 3.59/1.59  tff('#skF_13', type, '#skF_13': $i).
% 3.59/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.59/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.59/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/1.59  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.59/1.59  tff('#skF_12', type, '#skF_12': $i > $i).
% 3.59/1.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.59/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.59/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.59/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.59  
% 3.59/1.60  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.59/1.60  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.59/1.60  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.59/1.60  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.59/1.60  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.59/1.60  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.59/1.60  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.59/1.60  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.59/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.59/1.60  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.59/1.60  tff(c_48, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.60  tff(c_308, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.60  tff(c_312, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_48, c_308])).
% 3.59/1.60  tff(c_54, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')!='#skF_10' | r2_hidden('#skF_13', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.60  tff(c_102, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')!='#skF_10'), inference(splitLeft, [status(thm)], [c_54])).
% 3.59/1.60  tff(c_313, plain, (k1_relat_1('#skF_11')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_102])).
% 3.59/1.60  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.59/1.60  tff(c_60, plain, (![D_50]: (r2_hidden(k4_tarski(D_50, '#skF_12'(D_50)), '#skF_11') | ~r2_hidden(D_50, '#skF_10') | k1_relset_1('#skF_10', '#skF_9', '#skF_11')='#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.60  tff(c_246, plain, (![D_94]: (r2_hidden(k4_tarski(D_94, '#skF_12'(D_94)), '#skF_11') | ~r2_hidden(D_94, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_102, c_60])).
% 3.59/1.60  tff(c_34, plain, (![C_34, A_19, D_37]: (r2_hidden(C_34, k1_relat_1(A_19)) | ~r2_hidden(k4_tarski(C_34, D_37), A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.59/1.60  tff(c_290, plain, (![D_97]: (r2_hidden(D_97, k1_relat_1('#skF_11')) | ~r2_hidden(D_97, '#skF_10'))), inference(resolution, [status(thm)], [c_246, c_34])).
% 3.59/1.60  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.59/1.60  tff(c_634, plain, (![A_146]: (r1_tarski(A_146, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_2'(A_146, k1_relat_1('#skF_11')), '#skF_10'))), inference(resolution, [status(thm)], [c_290, c_8])).
% 3.59/1.60  tff(c_642, plain, (r1_tarski('#skF_10', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_10, c_634])).
% 3.59/1.60  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.59/1.60  tff(c_667, plain, (k1_relat_1('#skF_11')='#skF_10' | ~r1_tarski(k1_relat_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_642, c_12])).
% 3.59/1.60  tff(c_678, plain, (~r1_tarski(k1_relat_1('#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_313, c_667])).
% 3.59/1.60  tff(c_1275, plain, (![A_200, B_201, C_202]: (m1_subset_1(k1_relset_1(A_200, B_201, C_202), k1_zfmisc_1(A_200)) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.59/1.60  tff(c_1285, plain, (m1_subset_1(k1_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_312, c_1275])).
% 3.59/1.60  tff(c_1289, plain, (m1_subset_1(k1_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1285])).
% 3.59/1.60  tff(c_85, plain, (![A_64, B_65]: (r2_hidden(A_64, B_65) | v1_xboole_0(B_65) | ~m1_subset_1(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/1.60  tff(c_18, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.59/1.60  tff(c_93, plain, (![A_64, A_12]: (r1_tarski(A_64, A_12) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~m1_subset_1(A_64, k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_85, c_18])).
% 3.59/1.60  tff(c_1292, plain, (r1_tarski(k1_relat_1('#skF_11'), '#skF_10') | v1_xboole_0(k1_zfmisc_1('#skF_10'))), inference(resolution, [status(thm)], [c_1289, c_93])).
% 3.59/1.60  tff(c_1295, plain, (v1_xboole_0(k1_zfmisc_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_678, c_1292])).
% 3.59/1.60  tff(c_69, plain, (![C_58, A_59]: (r2_hidden(C_58, k1_zfmisc_1(A_59)) | ~r1_tarski(C_58, A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.59/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.59/1.60  tff(c_73, plain, (![A_59, C_58]: (~v1_xboole_0(k1_zfmisc_1(A_59)) | ~r1_tarski(C_58, A_59))), inference(resolution, [status(thm)], [c_69, c_2])).
% 3.59/1.60  tff(c_1302, plain, (![C_203]: (~r1_tarski(C_203, '#skF_10'))), inference(resolution, [status(thm)], [c_1295, c_73])).
% 3.59/1.60  tff(c_1343, plain, $false, inference(resolution, [status(thm)], [c_16, c_1302])).
% 3.59/1.60  tff(c_1344, plain, (r2_hidden('#skF_13', '#skF_10')), inference(splitRight, [status(thm)], [c_54])).
% 3.59/1.60  tff(c_1345, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 3.59/1.60  tff(c_50, plain, (![E_53]: (k1_relset_1('#skF_10', '#skF_9', '#skF_11')!='#skF_10' | ~r2_hidden(k4_tarski('#skF_13', E_53), '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.60  tff(c_1346, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')!='#skF_10'), inference(splitLeft, [status(thm)], [c_50])).
% 3.59/1.60  tff(c_1356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1346])).
% 3.59/1.60  tff(c_1358, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.60  tff(c_1496, plain, (![A_228, B_229, C_230]: (k1_relset_1(A_228, B_229, C_230)=k1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.60  tff(c_1499, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_48, c_1496])).
% 3.59/1.60  tff(c_1501, plain, (k1_relat_1('#skF_11')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_1499])).
% 3.59/1.60  tff(c_1772, plain, (![C_270, A_271]: (r2_hidden(k4_tarski(C_270, '#skF_8'(A_271, k1_relat_1(A_271), C_270)), A_271) | ~r2_hidden(C_270, k1_relat_1(A_271)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.59/1.60  tff(c_1357, plain, (![E_53]: (~r2_hidden(k4_tarski('#skF_13', E_53), '#skF_11'))), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.60  tff(c_1781, plain, (~r2_hidden('#skF_13', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_1772, c_1357])).
% 3.59/1.60  tff(c_1797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1344, c_1501, c_1781])).
% 3.59/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.60  
% 3.59/1.60  Inference rules
% 3.59/1.60  ----------------------
% 3.59/1.60  #Ref     : 0
% 3.59/1.60  #Sup     : 393
% 3.59/1.60  #Fact    : 0
% 3.59/1.60  #Define  : 0
% 3.59/1.60  #Split   : 14
% 3.59/1.60  #Chain   : 0
% 3.59/1.60  #Close   : 0
% 3.59/1.60  
% 3.59/1.60  Ordering : KBO
% 3.59/1.60  
% 3.59/1.60  Simplification rules
% 3.59/1.60  ----------------------
% 3.59/1.60  #Subsume      : 110
% 3.59/1.60  #Demod        : 29
% 3.59/1.60  #Tautology    : 46
% 3.59/1.60  #SimpNegUnit  : 12
% 3.59/1.60  #BackRed      : 3
% 3.59/1.60  
% 3.59/1.60  #Partial instantiations: 0
% 3.59/1.60  #Strategies tried      : 1
% 3.59/1.60  
% 3.59/1.60  Timing (in seconds)
% 3.59/1.60  ----------------------
% 3.59/1.60  Preprocessing        : 0.32
% 3.59/1.61  Parsing              : 0.16
% 3.59/1.61  CNF conversion       : 0.03
% 3.59/1.61  Main loop            : 0.52
% 3.59/1.61  Inferencing          : 0.19
% 3.59/1.61  Reduction            : 0.13
% 3.59/1.61  Demodulation         : 0.09
% 3.59/1.61  BG Simplification    : 0.03
% 3.59/1.61  Subsumption          : 0.12
% 3.59/1.61  Abstraction          : 0.03
% 3.59/1.61  MUC search           : 0.00
% 3.59/1.61  Cooper               : 0.00
% 3.59/1.61  Total                : 0.87
% 3.59/1.61  Index Insertion      : 0.00
% 3.59/1.61  Index Deletion       : 0.00
% 3.59/1.61  Index Matching       : 0.00
% 3.59/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
