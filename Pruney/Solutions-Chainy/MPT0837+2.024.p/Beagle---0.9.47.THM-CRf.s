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
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 17.30s
% Output     : CNFRefutation 17.30s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 153 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 347 expanded)
%              Number of equality atoms :    6 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16019,plain,(
    ! [A_800,B_801,C_802] :
      ( k2_relset_1(A_800,B_801,C_802) = k2_relat_1(C_802)
      | ~ m1_subset_1(C_802,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16028,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_16019])).

tff(c_48,plain,
    ( m1_subset_1('#skF_9','#skF_6')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_16031,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16028,c_66])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16061,plain,(
    ! [A_807,C_808] :
      ( r2_hidden(k4_tarski('#skF_4'(A_807,k2_relat_1(A_807),C_808),C_808),A_807)
      | ~ r2_hidden(C_808,k2_relat_1(A_807)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40036,plain,(
    ! [A_1552,C_1553,A_1554] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1552,k2_relat_1(A_1552),C_1553),C_1553),A_1554)
      | ~ m1_subset_1(A_1552,k1_zfmisc_1(A_1554))
      | ~ r2_hidden(C_1553,k2_relat_1(A_1552)) ) ),
    inference(resolution,[status(thm)],[c_16061,c_16])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58438,plain,(
    ! [A_1934,C_1935,C_1936,D_1937] :
      ( r2_hidden('#skF_4'(A_1934,k2_relat_1(A_1934),C_1935),C_1936)
      | ~ m1_subset_1(A_1934,k1_zfmisc_1(k2_zfmisc_1(C_1936,D_1937)))
      | ~ r2_hidden(C_1935,k2_relat_1(A_1934)) ) ),
    inference(resolution,[status(thm)],[c_40036,c_6])).

tff(c_58466,plain,(
    ! [C_1938] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1938),'#skF_6')
      | ~ r2_hidden(C_1938,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_32,c_58438])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58503,plain,(
    ! [C_1938] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1938),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(C_1938,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_58466,c_8])).

tff(c_58524,plain,(
    ! [C_1939] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1939),'#skF_6')
      | ~ r2_hidden(C_1939,k2_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_58503])).

tff(c_18,plain,(
    ! [A_11,C_26] :
      ( r2_hidden(k4_tarski('#skF_4'(A_11,k2_relat_1(A_11),C_26),C_26),A_11)
      | ~ r2_hidden(C_26,k2_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19547,plain,(
    ! [A_1020,C_1021,A_1022] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1020,k2_relat_1(A_1020),C_1021),C_1021),A_1022)
      | ~ m1_subset_1(A_1020,k1_zfmisc_1(A_1022))
      | ~ r2_hidden(C_1021,k2_relat_1(A_1020)) ) ),
    inference(resolution,[status(thm)],[c_16061,c_16])).

tff(c_37385,plain,(
    ! [A_1363,C_1364,C_1365,D_1366] :
      ( r2_hidden('#skF_4'(A_1363,k2_relat_1(A_1363),C_1364),C_1365)
      | ~ m1_subset_1(A_1363,k1_zfmisc_1(k2_zfmisc_1(C_1365,D_1366)))
      | ~ r2_hidden(C_1364,k2_relat_1(A_1363)) ) ),
    inference(resolution,[status(thm)],[c_19547,c_6])).

tff(c_37417,plain,(
    ! [C_1367] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1367),'#skF_6')
      | ~ r2_hidden(C_1367,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_32,c_37385])).

tff(c_37456,plain,(
    ! [C_1367] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1367),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(C_1367,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_37417,c_8])).

tff(c_37478,plain,(
    ! [C_1368] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1368),'#skF_6')
      | ~ r2_hidden(C_1368,k2_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_37456])).

tff(c_40,plain,(
    ! [E_74] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
      | ~ r2_hidden(k4_tarski(E_74,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16095,plain,(
    ! [E_812] :
      ( ~ r2_hidden(k4_tarski(E_812,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_812,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_16099,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_18,c_16095])).

tff(c_16105,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16031,c_16099])).

tff(c_37487,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_37478,c_16105])).

tff(c_37499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16031,c_37487])).

tff(c_37500,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_20,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k2_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(D_29,C_26),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37510,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_37500,c_20])).

tff(c_38,plain,(
    ! [E_74] :
      ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(E_74,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_37513,plain,(
    ! [E_74] :
      ( ~ r2_hidden('#skF_8',k2_relat_1('#skF_7'))
      | ~ r2_hidden(k4_tarski(E_74,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16028,c_38])).

tff(c_37514,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_37513])).

tff(c_37524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37510,c_37514])).

tff(c_37536,plain,(
    ! [E_1369] :
      ( ~ r2_hidden(k4_tarski(E_1369,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_1369,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_37513])).

tff(c_37540,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_18,c_37536])).

tff(c_37546,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16031,c_37540])).

tff(c_58533,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_58524,c_37546])).

tff(c_58545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16031,c_58533])).

tff(c_58547,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58577,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58547,c_46])).

tff(c_58587,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_58577,c_20])).

tff(c_58633,plain,(
    ! [A_1957,B_1958,C_1959] :
      ( k2_relset_1(A_1957,B_1958,C_1959) = k2_relat_1(C_1959)
      | ~ m1_subset_1(C_1959,k1_zfmisc_1(k2_zfmisc_1(A_1957,B_1958))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58642,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_58633])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58597,plain,(
    ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58547,c_44])).

tff(c_58643,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58642,c_58597])).

tff(c_58647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58587,c_58643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.30/9.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.30/9.17  
% 17.30/9.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.30/9.17  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 17.30/9.17  
% 17.30/9.17  %Foreground sorts:
% 17.30/9.17  
% 17.30/9.17  
% 17.30/9.17  %Background operators:
% 17.30/9.17  
% 17.30/9.17  
% 17.30/9.17  %Foreground operators:
% 17.30/9.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 17.30/9.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.30/9.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.30/9.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.30/9.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.30/9.17  tff('#skF_7', type, '#skF_7': $i).
% 17.30/9.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.30/9.17  tff('#skF_10', type, '#skF_10': $i).
% 17.30/9.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.30/9.17  tff('#skF_5', type, '#skF_5': $i).
% 17.30/9.17  tff('#skF_6', type, '#skF_6': $i).
% 17.30/9.17  tff('#skF_9', type, '#skF_9': $i).
% 17.30/9.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.30/9.17  tff('#skF_8', type, '#skF_8': $i).
% 17.30/9.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.30/9.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.30/9.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.30/9.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.30/9.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.30/9.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.30/9.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.30/9.17  
% 17.30/9.19  tff(f_82, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 17.30/9.19  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 17.30/9.19  tff(f_59, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 17.30/9.19  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 17.30/9.19  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 17.30/9.19  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 17.30/9.19  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_16019, plain, (![A_800, B_801, C_802]: (k2_relset_1(A_800, B_801, C_802)=k2_relat_1(C_802) | ~m1_subset_1(C_802, k1_zfmisc_1(k2_zfmisc_1(A_800, B_801))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.30/9.19  tff(c_16028, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_16019])).
% 17.30/9.19  tff(c_48, plain, (m1_subset_1('#skF_9', '#skF_6') | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_66, plain, (r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 17.30/9.19  tff(c_16031, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_16028, c_66])).
% 17.30/9.19  tff(c_34, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_16061, plain, (![A_807, C_808]: (r2_hidden(k4_tarski('#skF_4'(A_807, k2_relat_1(A_807), C_808), C_808), A_807) | ~r2_hidden(C_808, k2_relat_1(A_807)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.30/9.19  tff(c_16, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.30/9.19  tff(c_40036, plain, (![A_1552, C_1553, A_1554]: (r2_hidden(k4_tarski('#skF_4'(A_1552, k2_relat_1(A_1552), C_1553), C_1553), A_1554) | ~m1_subset_1(A_1552, k1_zfmisc_1(A_1554)) | ~r2_hidden(C_1553, k2_relat_1(A_1552)))), inference(resolution, [status(thm)], [c_16061, c_16])).
% 17.30/9.19  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.30/9.19  tff(c_58438, plain, (![A_1934, C_1935, C_1936, D_1937]: (r2_hidden('#skF_4'(A_1934, k2_relat_1(A_1934), C_1935), C_1936) | ~m1_subset_1(A_1934, k1_zfmisc_1(k2_zfmisc_1(C_1936, D_1937))) | ~r2_hidden(C_1935, k2_relat_1(A_1934)))), inference(resolution, [status(thm)], [c_40036, c_6])).
% 17.30/9.19  tff(c_58466, plain, (![C_1938]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1938), '#skF_6') | ~r2_hidden(C_1938, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_32, c_58438])).
% 17.30/9.19  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.30/9.19  tff(c_58503, plain, (![C_1938]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1938), '#skF_6') | v1_xboole_0('#skF_6') | ~r2_hidden(C_1938, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_58466, c_8])).
% 17.30/9.19  tff(c_58524, plain, (![C_1939]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1939), '#skF_6') | ~r2_hidden(C_1939, k2_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_34, c_58503])).
% 17.30/9.19  tff(c_18, plain, (![A_11, C_26]: (r2_hidden(k4_tarski('#skF_4'(A_11, k2_relat_1(A_11), C_26), C_26), A_11) | ~r2_hidden(C_26, k2_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.30/9.19  tff(c_19547, plain, (![A_1020, C_1021, A_1022]: (r2_hidden(k4_tarski('#skF_4'(A_1020, k2_relat_1(A_1020), C_1021), C_1021), A_1022) | ~m1_subset_1(A_1020, k1_zfmisc_1(A_1022)) | ~r2_hidden(C_1021, k2_relat_1(A_1020)))), inference(resolution, [status(thm)], [c_16061, c_16])).
% 17.30/9.19  tff(c_37385, plain, (![A_1363, C_1364, C_1365, D_1366]: (r2_hidden('#skF_4'(A_1363, k2_relat_1(A_1363), C_1364), C_1365) | ~m1_subset_1(A_1363, k1_zfmisc_1(k2_zfmisc_1(C_1365, D_1366))) | ~r2_hidden(C_1364, k2_relat_1(A_1363)))), inference(resolution, [status(thm)], [c_19547, c_6])).
% 17.30/9.19  tff(c_37417, plain, (![C_1367]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1367), '#skF_6') | ~r2_hidden(C_1367, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_32, c_37385])).
% 17.30/9.19  tff(c_37456, plain, (![C_1367]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1367), '#skF_6') | v1_xboole_0('#skF_6') | ~r2_hidden(C_1367, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_37417, c_8])).
% 17.30/9.19  tff(c_37478, plain, (![C_1368]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1368), '#skF_6') | ~r2_hidden(C_1368, k2_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_34, c_37456])).
% 17.30/9.19  tff(c_40, plain, (![E_74]: (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7') | ~r2_hidden(k4_tarski(E_74, '#skF_10'), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_16095, plain, (![E_812]: (~r2_hidden(k4_tarski(E_812, '#skF_10'), '#skF_7') | ~m1_subset_1(E_812, '#skF_6'))), inference(splitLeft, [status(thm)], [c_40])).
% 17.30/9.19  tff(c_16099, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6') | ~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_16095])).
% 17.30/9.19  tff(c_16105, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16031, c_16099])).
% 17.30/9.19  tff(c_37487, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_37478, c_16105])).
% 17.30/9.19  tff(c_37499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16031, c_37487])).
% 17.30/9.19  tff(c_37500, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_40])).
% 17.30/9.19  tff(c_20, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k2_relat_1(A_11)) | ~r2_hidden(k4_tarski(D_29, C_26), A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.30/9.19  tff(c_37510, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_37500, c_20])).
% 17.30/9.19  tff(c_38, plain, (![E_74]: (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~r2_hidden(k4_tarski(E_74, '#skF_10'), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_37513, plain, (![E_74]: (~r2_hidden('#skF_8', k2_relat_1('#skF_7')) | ~r2_hidden(k4_tarski(E_74, '#skF_10'), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16028, c_38])).
% 17.30/9.19  tff(c_37514, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_37513])).
% 17.30/9.19  tff(c_37524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37510, c_37514])).
% 17.30/9.19  tff(c_37536, plain, (![E_1369]: (~r2_hidden(k4_tarski(E_1369, '#skF_10'), '#skF_7') | ~m1_subset_1(E_1369, '#skF_6'))), inference(splitRight, [status(thm)], [c_37513])).
% 17.30/9.19  tff(c_37540, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6') | ~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_37536])).
% 17.30/9.19  tff(c_37546, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16031, c_37540])).
% 17.30/9.19  tff(c_58533, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_58524, c_37546])).
% 17.30/9.19  tff(c_58545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16031, c_58533])).
% 17.30/9.19  tff(c_58547, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 17.30/9.19  tff(c_46, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7') | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_58577, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58547, c_46])).
% 17.30/9.19  tff(c_58587, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_58577, c_20])).
% 17.30/9.19  tff(c_58633, plain, (![A_1957, B_1958, C_1959]: (k2_relset_1(A_1957, B_1958, C_1959)=k2_relat_1(C_1959) | ~m1_subset_1(C_1959, k1_zfmisc_1(k2_zfmisc_1(A_1957, B_1958))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.30/9.19  tff(c_58642, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_58633])).
% 17.30/9.19  tff(c_44, plain, (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7')) | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.30/9.19  tff(c_58597, plain, (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58547, c_44])).
% 17.30/9.19  tff(c_58643, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58642, c_58597])).
% 17.30/9.19  tff(c_58647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58587, c_58643])).
% 17.30/9.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.30/9.19  
% 17.30/9.19  Inference rules
% 17.30/9.19  ----------------------
% 17.30/9.19  #Ref     : 0
% 17.30/9.19  #Sup     : 16034
% 17.30/9.19  #Fact    : 2
% 17.30/9.19  #Define  : 0
% 17.30/9.19  #Split   : 43
% 17.30/9.19  #Chain   : 0
% 17.30/9.19  #Close   : 0
% 17.30/9.19  
% 17.30/9.19  Ordering : KBO
% 17.30/9.19  
% 17.30/9.19  Simplification rules
% 17.30/9.19  ----------------------
% 17.30/9.19  #Subsume      : 909
% 17.30/9.19  #Demod        : 210
% 17.30/9.19  #Tautology    : 335
% 17.30/9.19  #SimpNegUnit  : 65
% 17.30/9.19  #BackRed      : 111
% 17.30/9.19  
% 17.30/9.19  #Partial instantiations: 0
% 17.30/9.19  #Strategies tried      : 1
% 17.30/9.19  
% 17.30/9.19  Timing (in seconds)
% 17.30/9.19  ----------------------
% 17.30/9.19  Preprocessing        : 0.31
% 17.30/9.19  Parsing              : 0.16
% 17.30/9.19  CNF conversion       : 0.03
% 17.30/9.19  Main loop            : 8.10
% 17.30/9.19  Inferencing          : 1.33
% 17.30/9.19  Reduction            : 1.68
% 17.30/9.19  Demodulation         : 1.09
% 17.30/9.19  BG Simplification    : 0.28
% 17.30/9.19  Subsumption          : 4.06
% 17.30/9.19  Abstraction          : 0.33
% 17.30/9.19  MUC search           : 0.00
% 17.30/9.19  Cooper               : 0.00
% 17.30/9.19  Total                : 8.44
% 17.30/9.19  Index Insertion      : 0.00
% 17.30/9.19  Index Deletion       : 0.00
% 17.30/9.19  Index Matching       : 0.00
% 17.30/9.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
