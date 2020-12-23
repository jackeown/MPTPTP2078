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
% DateTime   : Thu Dec  3 10:08:04 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 148 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 323 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_36,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_299,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_303,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_299])).

tff(c_181,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_181])).

tff(c_52,plain,
    ( r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11'))
    | m1_subset_1('#skF_13','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_55,plain,(
    m1_subset_1('#skF_13','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11'))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k1_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(C_19,D_22),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_60,c_6])).

tff(c_71,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_42,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_92),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10')
      | ~ r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11')) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    ! [E_124] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_124),'#skF_11')
      | ~ m1_subset_1(E_124,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_75,c_42])).

tff(c_169,plain,(
    ~ m1_subset_1('#skF_13','#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_162])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_169])).

tff(c_177,plain,(
    r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_191,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_177])).

tff(c_252,plain,(
    ! [C_145,A_146] :
      ( r2_hidden(k4_tarski(C_145,'#skF_4'(A_146,k1_relat_1(A_146),C_145)),A_146)
      | ~ r2_hidden(C_145,k1_relat_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k2_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(D_41,C_38),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_275,plain,(
    ! [A_147,C_148] :
      ( r2_hidden('#skF_4'(A_147,k1_relat_1(A_147),C_148),k2_relat_1(A_147))
      | ~ r2_hidden(C_148,k1_relat_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_252,c_18])).

tff(c_186,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_190,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_186])).

tff(c_202,plain,(
    ! [A_133,B_134,C_135] :
      ( m1_subset_1(k2_relset_1(A_133,B_134,C_135),k1_zfmisc_1(B_134))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_215,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_202])).

tff(c_220,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_215])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_10')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_281,plain,(
    ! [C_149] :
      ( m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),C_149),'#skF_10')
      | ~ r2_hidden(C_149,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_275,c_223])).

tff(c_178,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_92),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10')
      | r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_200,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_92),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_46])).

tff(c_260,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_252,c_200])).

tff(c_270,plain,(
    ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_260])).

tff(c_284,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_281,c_270])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_284])).

tff(c_289,plain,(
    r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_304,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_289])).

tff(c_364,plain,(
    ! [C_171,A_172] :
      ( r2_hidden(k4_tarski(C_171,'#skF_4'(A_172,k1_relat_1(A_172),C_171)),A_172)
      | ~ r2_hidden(C_171,k1_relat_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_385,plain,(
    ! [A_173,C_174] :
      ( r2_hidden('#skF_4'(A_173,k1_relat_1(A_173),C_174),k2_relat_1(A_173))
      | ~ r2_hidden(C_174,k1_relat_1(A_173)) ) ),
    inference(resolution,[status(thm)],[c_364,c_18])).

tff(c_309,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_313,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_309])).

tff(c_329,plain,(
    ! [A_167,B_168,C_169] :
      ( m1_subset_1(k2_relset_1(A_167,B_168,C_169),k1_zfmisc_1(B_168))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_342,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_329])).

tff(c_347,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_342])).

tff(c_350,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_10')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_347,c_2])).

tff(c_391,plain,(
    ! [C_175] :
      ( m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),C_175),'#skF_10')
      | ~ r2_hidden(C_175,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_385,c_350])).

tff(c_290,plain,(
    ~ m1_subset_1('#skF_13','#skF_10') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_92),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10')
      | m1_subset_1('#skF_13','#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_297,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_92),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_50])).

tff(c_372,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_364,c_297])).

tff(c_382,plain,(
    ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_372])).

tff(c_394,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_391,c_382])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  
% 2.44/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 2.44/1.37  
% 2.44/1.37  %Foreground sorts:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Background operators:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Foreground operators:
% 2.44/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.37  tff('#skF_11', type, '#skF_11': $i).
% 2.44/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.44/1.37  tff('#skF_10', type, '#skF_10': $i).
% 2.44/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.37  tff('#skF_13', type, '#skF_13': $i).
% 2.44/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.44/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.44/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.37  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.44/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.44/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.37  tff('#skF_12', type, '#skF_12': $i).
% 2.44/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.37  
% 2.44/1.39  tff(f_80, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 2.44/1.39  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.44/1.39  tff(f_39, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.44/1.39  tff(f_47, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.44/1.39  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.44/1.39  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.44/1.39  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.44/1.39  tff(c_36, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.39  tff(c_299, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.39  tff(c_303, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_299])).
% 2.44/1.39  tff(c_181, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.39  tff(c_185, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_181])).
% 2.44/1.39  tff(c_52, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11')) | m1_subset_1('#skF_13', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.39  tff(c_55, plain, (m1_subset_1('#skF_13', '#skF_10')), inference(splitLeft, [status(thm)], [c_52])).
% 2.44/1.39  tff(c_48, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11')) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.39  tff(c_60, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11')), inference(splitLeft, [status(thm)], [c_48])).
% 2.44/1.39  tff(c_6, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k1_relat_1(A_4)) | ~r2_hidden(k4_tarski(C_19, D_22), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.44/1.39  tff(c_67, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_60, c_6])).
% 2.44/1.39  tff(c_71, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.39  tff(c_75, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.44/1.39  tff(c_42, plain, (![E_92]: (~r2_hidden(k4_tarski('#skF_12', E_92), '#skF_11') | ~m1_subset_1(E_92, '#skF_10') | ~r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.39  tff(c_162, plain, (![E_124]: (~r2_hidden(k4_tarski('#skF_12', E_124), '#skF_11') | ~m1_subset_1(E_124, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_75, c_42])).
% 2.44/1.39  tff(c_169, plain, (~m1_subset_1('#skF_13', '#skF_10')), inference(resolution, [status(thm)], [c_60, c_162])).
% 2.44/1.39  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_169])).
% 2.44/1.39  tff(c_177, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_48])).
% 2.44/1.39  tff(c_191, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_177])).
% 2.44/1.39  tff(c_252, plain, (![C_145, A_146]: (r2_hidden(k4_tarski(C_145, '#skF_4'(A_146, k1_relat_1(A_146), C_145)), A_146) | ~r2_hidden(C_145, k1_relat_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.44/1.39  tff(c_18, plain, (![C_38, A_23, D_41]: (r2_hidden(C_38, k2_relat_1(A_23)) | ~r2_hidden(k4_tarski(D_41, C_38), A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.44/1.39  tff(c_275, plain, (![A_147, C_148]: (r2_hidden('#skF_4'(A_147, k1_relat_1(A_147), C_148), k2_relat_1(A_147)) | ~r2_hidden(C_148, k1_relat_1(A_147)))), inference(resolution, [status(thm)], [c_252, c_18])).
% 2.44/1.39  tff(c_186, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.39  tff(c_190, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_186])).
% 2.44/1.39  tff(c_202, plain, (![A_133, B_134, C_135]: (m1_subset_1(k2_relset_1(A_133, B_134, C_135), k1_zfmisc_1(B_134)) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.44/1.39  tff(c_215, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_190, c_202])).
% 2.44/1.39  tff(c_220, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_215])).
% 2.44/1.39  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.39  tff(c_223, plain, (![A_1]: (m1_subset_1(A_1, '#skF_10') | ~r2_hidden(A_1, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_220, c_2])).
% 2.44/1.39  tff(c_281, plain, (![C_149]: (m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), C_149), '#skF_10') | ~r2_hidden(C_149, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_275, c_223])).
% 2.44/1.39  tff(c_178, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11')), inference(splitRight, [status(thm)], [c_48])).
% 2.44/1.39  tff(c_46, plain, (![E_92]: (~r2_hidden(k4_tarski('#skF_12', E_92), '#skF_11') | ~m1_subset_1(E_92, '#skF_10') | r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.39  tff(c_200, plain, (![E_92]: (~r2_hidden(k4_tarski('#skF_12', E_92), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_178, c_46])).
% 2.44/1.39  tff(c_260, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_252, c_200])).
% 2.44/1.39  tff(c_270, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_260])).
% 2.44/1.39  tff(c_284, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_281, c_270])).
% 2.44/1.39  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_284])).
% 2.44/1.39  tff(c_289, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_52])).
% 2.44/1.39  tff(c_304, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_289])).
% 2.44/1.39  tff(c_364, plain, (![C_171, A_172]: (r2_hidden(k4_tarski(C_171, '#skF_4'(A_172, k1_relat_1(A_172), C_171)), A_172) | ~r2_hidden(C_171, k1_relat_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.44/1.39  tff(c_385, plain, (![A_173, C_174]: (r2_hidden('#skF_4'(A_173, k1_relat_1(A_173), C_174), k2_relat_1(A_173)) | ~r2_hidden(C_174, k1_relat_1(A_173)))), inference(resolution, [status(thm)], [c_364, c_18])).
% 2.44/1.39  tff(c_309, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.39  tff(c_313, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_309])).
% 2.44/1.39  tff(c_329, plain, (![A_167, B_168, C_169]: (m1_subset_1(k2_relset_1(A_167, B_168, C_169), k1_zfmisc_1(B_168)) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.44/1.39  tff(c_342, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_313, c_329])).
% 2.44/1.39  tff(c_347, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_342])).
% 2.44/1.39  tff(c_350, plain, (![A_1]: (m1_subset_1(A_1, '#skF_10') | ~r2_hidden(A_1, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_347, c_2])).
% 2.44/1.39  tff(c_391, plain, (![C_175]: (m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), C_175), '#skF_10') | ~r2_hidden(C_175, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_385, c_350])).
% 2.44/1.39  tff(c_290, plain, (~m1_subset_1('#skF_13', '#skF_10')), inference(splitRight, [status(thm)], [c_52])).
% 2.44/1.39  tff(c_50, plain, (![E_92]: (~r2_hidden(k4_tarski('#skF_12', E_92), '#skF_11') | ~m1_subset_1(E_92, '#skF_10') | m1_subset_1('#skF_13', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.39  tff(c_297, plain, (![E_92]: (~r2_hidden(k4_tarski('#skF_12', E_92), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_290, c_50])).
% 2.44/1.39  tff(c_372, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_364, c_297])).
% 2.44/1.39  tff(c_382, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_372])).
% 2.44/1.39  tff(c_394, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_391, c_382])).
% 2.44/1.39  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_304, c_394])).
% 2.44/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.39  
% 2.44/1.39  Inference rules
% 2.44/1.39  ----------------------
% 2.44/1.39  #Ref     : 0
% 2.44/1.39  #Sup     : 69
% 2.44/1.39  #Fact    : 0
% 2.44/1.39  #Define  : 0
% 2.44/1.39  #Split   : 2
% 2.44/1.39  #Chain   : 0
% 2.44/1.39  #Close   : 0
% 2.44/1.39  
% 2.44/1.39  Ordering : KBO
% 2.44/1.39  
% 2.44/1.39  Simplification rules
% 2.44/1.39  ----------------------
% 2.44/1.39  #Subsume      : 3
% 2.44/1.39  #Demod        : 22
% 2.44/1.39  #Tautology    : 24
% 2.44/1.39  #SimpNegUnit  : 2
% 2.44/1.39  #BackRed      : 2
% 2.44/1.39  
% 2.44/1.39  #Partial instantiations: 0
% 2.44/1.39  #Strategies tried      : 1
% 2.44/1.39  
% 2.44/1.39  Timing (in seconds)
% 2.44/1.39  ----------------------
% 2.44/1.39  Preprocessing        : 0.34
% 2.44/1.39  Parsing              : 0.17
% 2.44/1.39  CNF conversion       : 0.03
% 2.44/1.39  Main loop            : 0.27
% 2.44/1.39  Inferencing          : 0.11
% 2.44/1.39  Reduction            : 0.08
% 2.44/1.39  Demodulation         : 0.05
% 2.44/1.39  BG Simplification    : 0.02
% 2.44/1.39  Subsumption          : 0.04
% 2.44/1.39  Abstraction          : 0.02
% 2.44/1.39  MUC search           : 0.00
% 2.44/1.39  Cooper               : 0.00
% 2.44/1.39  Total                : 0.65
% 2.44/1.39  Index Insertion      : 0.00
% 2.44/1.39  Index Deletion       : 0.00
% 2.44/1.39  Index Matching       : 0.00
% 2.44/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
