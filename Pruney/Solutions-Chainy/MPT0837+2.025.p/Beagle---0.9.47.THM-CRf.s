%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 10.89s
% Output     : CNFRefutation 10.89s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 151 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  112 ( 325 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4618,plain,(
    ! [A_427,B_428,C_429] :
      ( k2_relset_1(A_427,B_428,C_429) = k2_relat_1(C_429)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4637,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_4618])).

tff(c_50,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_73,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4641,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4637,c_73])).

tff(c_63,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_63,c_4])).

tff(c_53,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_9811,plain,(
    ! [A_771,C_772] :
      ( r2_hidden(k4_tarski('#skF_5'(A_771,k2_relat_1(A_771),C_772),C_772),A_771)
      | ~ r2_hidden(C_772,k2_relat_1(A_771)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11250,plain,(
    ! [A_915,C_916,B_917] :
      ( r2_hidden(k4_tarski('#skF_5'(A_915,k2_relat_1(A_915),C_916),C_916),B_917)
      | ~ r1_tarski(A_915,B_917)
      | ~ r2_hidden(C_916,k2_relat_1(A_915)) ) ),
    inference(resolution,[status(thm)],[c_9811,c_2])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16603,plain,(
    ! [A_1165,C_1166,C_1167,D_1168] :
      ( r2_hidden('#skF_5'(A_1165,k2_relat_1(A_1165),C_1166),C_1167)
      | ~ r1_tarski(A_1165,k2_zfmisc_1(C_1167,D_1168))
      | ~ r2_hidden(C_1166,k2_relat_1(A_1165)) ) ),
    inference(resolution,[status(thm)],[c_11250,c_12])).

tff(c_16650,plain,(
    ! [C_1169] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1169),'#skF_7')
      | ~ r2_hidden(C_1169,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_61,c_16603])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16667,plain,(
    ! [C_1170] :
      ( m1_subset_1('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1170),'#skF_7')
      | ~ r2_hidden(C_1170,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_16650,c_14])).

tff(c_4792,plain,(
    ! [A_460,C_461] :
      ( r2_hidden(k4_tarski('#skF_5'(A_460,k2_relat_1(A_460),C_461),C_461),A_460)
      | ~ r2_hidden(C_461,k2_relat_1(A_460)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5644,plain,(
    ! [A_557,C_558,B_559] :
      ( r2_hidden(k4_tarski('#skF_5'(A_557,k2_relat_1(A_557),C_558),C_558),B_559)
      | ~ r1_tarski(A_557,B_559)
      | ~ r2_hidden(C_558,k2_relat_1(A_557)) ) ),
    inference(resolution,[status(thm)],[c_4792,c_2])).

tff(c_9649,plain,(
    ! [A_755,C_756,C_757,D_758] :
      ( r2_hidden('#skF_5'(A_755,k2_relat_1(A_755),C_756),C_757)
      | ~ r1_tarski(A_755,k2_zfmisc_1(C_757,D_758))
      | ~ r2_hidden(C_756,k2_relat_1(A_755)) ) ),
    inference(resolution,[status(thm)],[c_5644,c_12])).

tff(c_9700,plain,(
    ! [C_759] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_759),'#skF_7')
      | ~ r2_hidden(C_759,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_61,c_9649])).

tff(c_9714,plain,(
    ! [C_760] :
      ( m1_subset_1('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_760),'#skF_7')
      | ~ r2_hidden(C_760,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_9700,c_14])).

tff(c_42,plain,(
    ! [E_77] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_77,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4654,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski(E_77,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_5691,plain,(
    ! [A_557] :
      ( ~ m1_subset_1('#skF_5'(A_557,k2_relat_1(A_557),'#skF_11'),'#skF_7')
      | ~ r1_tarski(A_557,'#skF_8')
      | ~ r2_hidden('#skF_11',k2_relat_1(A_557)) ) ),
    inference(resolution,[status(thm)],[c_5644,c_4654])).

tff(c_9718,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9714,c_5691])).

tff(c_9725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4641,c_71,c_9718])).

tff(c_9726,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k2_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(D_32,C_29),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9735,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9726,c_22])).

tff(c_40,plain,(
    ! [E_77] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_77,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9738,plain,(
    ! [E_77] :
      ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
      | ~ r2_hidden(k4_tarski(E_77,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4637,c_40])).

tff(c_9739,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_9738])).

tff(c_9748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9735,c_9739])).

tff(c_9749,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski(E_77,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_9738])).

tff(c_11289,plain,(
    ! [A_915] :
      ( ~ m1_subset_1('#skF_5'(A_915,k2_relat_1(A_915),'#skF_11'),'#skF_7')
      | ~ r1_tarski(A_915,'#skF_8')
      | ~ r2_hidden('#skF_11',k2_relat_1(A_915)) ) ),
    inference(resolution,[status(thm)],[c_11250,c_9749])).

tff(c_16671,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_16667,c_11289])).

tff(c_16678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4641,c_71,c_16671])).

tff(c_16680,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16697,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_16680,c_48])).

tff(c_16706,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_16697,c_22])).

tff(c_16746,plain,(
    ! [A_1192,B_1193,C_1194] :
      ( k2_relset_1(A_1192,B_1193,C_1194) = k2_relat_1(C_1194)
      | ~ m1_subset_1(C_1194,k1_zfmisc_1(k2_zfmisc_1(A_1192,B_1193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16760,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_16746])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16709,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_16680,c_46])).

tff(c_16761,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16760,c_16709])).

tff(c_16765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16706,c_16761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.89/4.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.03  
% 10.89/4.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 10.89/4.04  
% 10.89/4.04  %Foreground sorts:
% 10.89/4.04  
% 10.89/4.04  
% 10.89/4.04  %Background operators:
% 10.89/4.04  
% 10.89/4.04  
% 10.89/4.04  %Foreground operators:
% 10.89/4.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.89/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.89/4.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.89/4.04  tff('#skF_11', type, '#skF_11': $i).
% 10.89/4.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.89/4.04  tff('#skF_7', type, '#skF_7': $i).
% 10.89/4.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.89/4.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.89/4.04  tff('#skF_10', type, '#skF_10': $i).
% 10.89/4.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.89/4.04  tff('#skF_6', type, '#skF_6': $i).
% 10.89/4.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.89/4.04  tff('#skF_9', type, '#skF_9': $i).
% 10.89/4.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.89/4.04  tff('#skF_8', type, '#skF_8': $i).
% 10.89/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.89/4.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.89/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.89/4.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.89/4.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.89/4.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.89/4.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.89/4.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.89/4.04  
% 10.89/4.05  tff(f_77, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 10.89/4.05  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.89/4.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.89/4.05  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.89/4.05  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.89/4.05  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.89/4.05  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.89/4.05  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.89/4.05  tff(c_4618, plain, (![A_427, B_428, C_429]: (k2_relset_1(A_427, B_428, C_429)=k2_relat_1(C_429) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.89/4.05  tff(c_4637, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_4618])).
% 10.89/4.05  tff(c_50, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.89/4.05  tff(c_73, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 10.89/4.05  tff(c_4641, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4637, c_73])).
% 10.89/4.05  tff(c_63, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.89/4.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.89/4.05  tff(c_71, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_63, c_4])).
% 10.89/4.05  tff(c_53, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | ~m1_subset_1(A_82, k1_zfmisc_1(B_83)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.89/4.05  tff(c_61, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_53])).
% 10.89/4.05  tff(c_9811, plain, (![A_771, C_772]: (r2_hidden(k4_tarski('#skF_5'(A_771, k2_relat_1(A_771), C_772), C_772), A_771) | ~r2_hidden(C_772, k2_relat_1(A_771)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.89/4.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.89/4.05  tff(c_11250, plain, (![A_915, C_916, B_917]: (r2_hidden(k4_tarski('#skF_5'(A_915, k2_relat_1(A_915), C_916), C_916), B_917) | ~r1_tarski(A_915, B_917) | ~r2_hidden(C_916, k2_relat_1(A_915)))), inference(resolution, [status(thm)], [c_9811, c_2])).
% 10.89/4.05  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.89/4.05  tff(c_16603, plain, (![A_1165, C_1166, C_1167, D_1168]: (r2_hidden('#skF_5'(A_1165, k2_relat_1(A_1165), C_1166), C_1167) | ~r1_tarski(A_1165, k2_zfmisc_1(C_1167, D_1168)) | ~r2_hidden(C_1166, k2_relat_1(A_1165)))), inference(resolution, [status(thm)], [c_11250, c_12])).
% 10.89/4.05  tff(c_16650, plain, (![C_1169]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_1169), '#skF_7') | ~r2_hidden(C_1169, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_61, c_16603])).
% 10.89/4.05  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.89/4.05  tff(c_16667, plain, (![C_1170]: (m1_subset_1('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_1170), '#skF_7') | ~r2_hidden(C_1170, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_16650, c_14])).
% 10.89/4.05  tff(c_4792, plain, (![A_460, C_461]: (r2_hidden(k4_tarski('#skF_5'(A_460, k2_relat_1(A_460), C_461), C_461), A_460) | ~r2_hidden(C_461, k2_relat_1(A_460)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.89/4.05  tff(c_5644, plain, (![A_557, C_558, B_559]: (r2_hidden(k4_tarski('#skF_5'(A_557, k2_relat_1(A_557), C_558), C_558), B_559) | ~r1_tarski(A_557, B_559) | ~r2_hidden(C_558, k2_relat_1(A_557)))), inference(resolution, [status(thm)], [c_4792, c_2])).
% 10.89/4.05  tff(c_9649, plain, (![A_755, C_756, C_757, D_758]: (r2_hidden('#skF_5'(A_755, k2_relat_1(A_755), C_756), C_757) | ~r1_tarski(A_755, k2_zfmisc_1(C_757, D_758)) | ~r2_hidden(C_756, k2_relat_1(A_755)))), inference(resolution, [status(thm)], [c_5644, c_12])).
% 10.89/4.05  tff(c_9700, plain, (![C_759]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_759), '#skF_7') | ~r2_hidden(C_759, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_61, c_9649])).
% 10.89/4.05  tff(c_9714, plain, (![C_760]: (m1_subset_1('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_760), '#skF_7') | ~r2_hidden(C_760, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_9700, c_14])).
% 10.89/4.05  tff(c_42, plain, (![E_77]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_77, '#skF_11'), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.89/4.05  tff(c_4654, plain, (![E_77]: (~r2_hidden(k4_tarski(E_77, '#skF_11'), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(splitLeft, [status(thm)], [c_42])).
% 10.89/4.05  tff(c_5691, plain, (![A_557]: (~m1_subset_1('#skF_5'(A_557, k2_relat_1(A_557), '#skF_11'), '#skF_7') | ~r1_tarski(A_557, '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1(A_557)))), inference(resolution, [status(thm)], [c_5644, c_4654])).
% 10.89/4.05  tff(c_9718, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9714, c_5691])).
% 10.89/4.05  tff(c_9725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4641, c_71, c_9718])).
% 10.89/4.05  tff(c_9726, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_42])).
% 10.89/4.05  tff(c_22, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k2_relat_1(A_14)) | ~r2_hidden(k4_tarski(D_32, C_29), A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.89/4.05  tff(c_9735, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9726, c_22])).
% 10.89/4.05  tff(c_40, plain, (![E_77]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_77, '#skF_11'), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.89/4.05  tff(c_9738, plain, (![E_77]: (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | ~r2_hidden(k4_tarski(E_77, '#skF_11'), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4637, c_40])).
% 10.89/4.05  tff(c_9739, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_9738])).
% 10.89/4.05  tff(c_9748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9735, c_9739])).
% 10.89/4.05  tff(c_9749, plain, (![E_77]: (~r2_hidden(k4_tarski(E_77, '#skF_11'), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(splitRight, [status(thm)], [c_9738])).
% 10.89/4.05  tff(c_11289, plain, (![A_915]: (~m1_subset_1('#skF_5'(A_915, k2_relat_1(A_915), '#skF_11'), '#skF_7') | ~r1_tarski(A_915, '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1(A_915)))), inference(resolution, [status(thm)], [c_11250, c_9749])).
% 10.89/4.05  tff(c_16671, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16667, c_11289])).
% 10.89/4.05  tff(c_16678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4641, c_71, c_16671])).
% 10.89/4.05  tff(c_16680, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_50])).
% 10.89/4.05  tff(c_48, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.89/4.05  tff(c_16697, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_16680, c_48])).
% 10.89/4.05  tff(c_16706, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16697, c_22])).
% 10.89/4.05  tff(c_16746, plain, (![A_1192, B_1193, C_1194]: (k2_relset_1(A_1192, B_1193, C_1194)=k2_relat_1(C_1194) | ~m1_subset_1(C_1194, k1_zfmisc_1(k2_zfmisc_1(A_1192, B_1193))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.89/4.05  tff(c_16760, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_16746])).
% 10.89/4.05  tff(c_46, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.89/4.05  tff(c_16709, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_16680, c_46])).
% 10.89/4.05  tff(c_16761, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_16760, c_16709])).
% 10.89/4.05  tff(c_16765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16706, c_16761])).
% 10.89/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.05  
% 10.89/4.05  Inference rules
% 10.89/4.05  ----------------------
% 10.89/4.05  #Ref     : 0
% 10.89/4.05  #Sup     : 3949
% 10.89/4.05  #Fact    : 0
% 10.89/4.05  #Define  : 0
% 10.89/4.05  #Split   : 54
% 10.89/4.05  #Chain   : 0
% 10.89/4.05  #Close   : 0
% 10.89/4.05  
% 10.89/4.05  Ordering : KBO
% 10.89/4.05  
% 10.89/4.05  Simplification rules
% 10.89/4.05  ----------------------
% 10.89/4.05  #Subsume      : 592
% 10.89/4.05  #Demod        : 329
% 10.89/4.05  #Tautology    : 304
% 10.89/4.05  #SimpNegUnit  : 7
% 10.89/4.05  #BackRed      : 89
% 10.89/4.05  
% 10.89/4.05  #Partial instantiations: 0
% 10.89/4.05  #Strategies tried      : 1
% 10.89/4.05  
% 10.89/4.05  Timing (in seconds)
% 10.89/4.05  ----------------------
% 10.89/4.05  Preprocessing        : 0.33
% 10.89/4.05  Parsing              : 0.17
% 10.89/4.05  CNF conversion       : 0.03
% 10.89/4.05  Main loop            : 2.92
% 10.89/4.05  Inferencing          : 0.84
% 10.89/4.05  Reduction            : 0.80
% 10.89/4.05  Demodulation         : 0.52
% 10.89/4.05  BG Simplification    : 0.10
% 10.89/4.05  Subsumption          : 0.92
% 10.89/4.05  Abstraction          : 0.13
% 10.89/4.05  MUC search           : 0.00
% 10.89/4.05  Cooper               : 0.00
% 10.89/4.05  Total                : 3.28
% 10.89/4.05  Index Insertion      : 0.00
% 10.89/4.05  Index Deletion       : 0.00
% 10.89/4.05  Index Matching       : 0.00
% 10.89/4.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
