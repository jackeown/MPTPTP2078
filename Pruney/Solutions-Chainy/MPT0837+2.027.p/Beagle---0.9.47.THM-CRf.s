%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 165 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 339 expanded)
%              Number of equality atoms :   10 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_14 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12

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

tff('#skF_14',type,(
    '#skF_14': $i )).

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

tff(f_78,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_34,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_163,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_167,plain,(
    k2_relset_1('#skF_10','#skF_9','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_163])).

tff(c_50,plain,
    ( m1_subset_1('#skF_13','#skF_10')
    | r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_53,plain,(
    r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_168,plain,(
    r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_53])).

tff(c_330,plain,(
    ! [A_154,C_155] :
      ( r2_hidden(k4_tarski('#skF_8'(A_154,k2_relat_1(A_154),C_155),C_155),A_154)
      | ~ r2_hidden(C_155,k2_relat_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k1_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(C_19,D_22),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_351,plain,(
    ! [A_156,C_157] :
      ( r2_hidden('#skF_8'(A_156,k2_relat_1(A_156),C_157),k1_relat_1(A_156))
      | ~ r2_hidden(C_157,k2_relat_1(A_156)) ) ),
    inference(resolution,[status(thm)],[c_330,c_6])).

tff(c_173,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_177,plain,(
    k1_relset_1('#skF_10','#skF_9','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_173])).

tff(c_184,plain,(
    ! [A_133,B_134,C_135] :
      ( m1_subset_1(k1_relset_1(A_133,B_134,C_135),k1_zfmisc_1(A_133))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_197,plain,
    ( m1_subset_1(k1_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_184])).

tff(c_202,plain,(
    m1_subset_1(k1_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_10')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_357,plain,(
    ! [C_158] :
      ( m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_158),'#skF_10')
      | ~ r2_hidden(C_158,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_351,c_305])).

tff(c_40,plain,(
    ! [E_92] :
      ( ~ r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_9','#skF_11'))
      | ~ r2_hidden(k4_tarski(E_92,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_270,plain,(
    ! [E_92] :
      ( ~ r2_hidden('#skF_12',k2_relat_1('#skF_11'))
      | ~ r2_hidden(k4_tarski(E_92,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_40])).

tff(c_271,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_234,plain,(
    ! [A_142,C_143] :
      ( r2_hidden(k4_tarski('#skF_8'(A_142,k2_relat_1(A_142),C_143),C_143),A_142)
      | ~ r2_hidden(C_143,k2_relat_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_255,plain,(
    ! [A_144,C_145] :
      ( r2_hidden('#skF_8'(A_144,k2_relat_1(A_144),C_145),k1_relat_1(A_144))
      | ~ r2_hidden(C_145,k2_relat_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_234,c_6])).

tff(c_206,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_10')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_261,plain,(
    ! [C_146] :
      ( m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_146),'#skF_10')
      | ~ r2_hidden(C_146,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_255,c_206])).

tff(c_42,plain,(
    ! [E_92] :
      ( r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11')
      | ~ r2_hidden(k4_tarski(E_92,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski(E_92,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_238,plain,
    ( ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10')
    | ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_234,c_203])).

tff(c_251,plain,(
    ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_238])).

tff(c_264,plain,(
    ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_261,c_251])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_264])).

tff(c_269,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_18,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k2_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(D_41,C_38),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_269,c_18])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_277])).

tff(c_283,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski(E_92,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_92,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_334,plain,
    ( ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10')
    | ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_330,c_283])).

tff(c_347,plain,(
    ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_334])).

tff(c_360,plain,(
    ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_357,c_347])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_360])).

tff(c_366,plain,(
    ~ r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11')
    | r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_373,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_48])).

tff(c_381,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_373,c_18])).

tff(c_392,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_396,plain,(
    k2_relset_1('#skF_10','#skF_9','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_392])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_9','#skF_11'))
    | r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_391,plain,(
    ~ r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_46])).

tff(c_397,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_391])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_14 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 2.30/1.30  
% 2.30/1.30  %Foreground sorts:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Background operators:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Foreground operators:
% 2.30/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.30/1.30  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.30  tff('#skF_11', type, '#skF_11': $i).
% 2.30/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.30/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.30/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.30/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.30  tff('#skF_14', type, '#skF_14': $i).
% 2.30/1.30  tff('#skF_13', type, '#skF_13': $i).
% 2.30/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.30/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.30/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.30  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.30/1.30  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.30/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.30/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.30  tff('#skF_12', type, '#skF_12': $i).
% 2.30/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.30  
% 2.30/1.31  tff(f_78, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 2.30/1.31  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.30/1.31  tff(f_47, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.30/1.31  tff(f_39, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.30/1.31  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.30/1.31  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.30/1.31  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.30/1.31  tff(c_34, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_163, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.30/1.31  tff(c_167, plain, (k2_relset_1('#skF_10', '#skF_9', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_34, c_163])).
% 2.30/1.31  tff(c_50, plain, (m1_subset_1('#skF_13', '#skF_10') | r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_53, plain, (r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.30/1.31  tff(c_168, plain, (r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_53])).
% 2.30/1.31  tff(c_330, plain, (![A_154, C_155]: (r2_hidden(k4_tarski('#skF_8'(A_154, k2_relat_1(A_154), C_155), C_155), A_154) | ~r2_hidden(C_155, k2_relat_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.31  tff(c_6, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k1_relat_1(A_4)) | ~r2_hidden(k4_tarski(C_19, D_22), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.31  tff(c_351, plain, (![A_156, C_157]: (r2_hidden('#skF_8'(A_156, k2_relat_1(A_156), C_157), k1_relat_1(A_156)) | ~r2_hidden(C_157, k2_relat_1(A_156)))), inference(resolution, [status(thm)], [c_330, c_6])).
% 2.30/1.31  tff(c_173, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.31  tff(c_177, plain, (k1_relset_1('#skF_10', '#skF_9', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_34, c_173])).
% 2.30/1.31  tff(c_184, plain, (![A_133, B_134, C_135]: (m1_subset_1(k1_relset_1(A_133, B_134, C_135), k1_zfmisc_1(A_133)) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.31  tff(c_197, plain, (m1_subset_1(k1_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_177, c_184])).
% 2.30/1.31  tff(c_202, plain, (m1_subset_1(k1_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_197])).
% 2.30/1.31  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.31  tff(c_305, plain, (![A_1]: (m1_subset_1(A_1, '#skF_10') | ~r2_hidden(A_1, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_202, c_2])).
% 2.30/1.31  tff(c_357, plain, (![C_158]: (m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), C_158), '#skF_10') | ~r2_hidden(C_158, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_351, c_305])).
% 2.30/1.31  tff(c_40, plain, (![E_92]: (~r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_9', '#skF_11')) | ~r2_hidden(k4_tarski(E_92, '#skF_14'), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_270, plain, (![E_92]: (~r2_hidden('#skF_12', k2_relat_1('#skF_11')) | ~r2_hidden(k4_tarski(E_92, '#skF_14'), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_40])).
% 2.30/1.31  tff(c_271, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_270])).
% 2.30/1.31  tff(c_234, plain, (![A_142, C_143]: (r2_hidden(k4_tarski('#skF_8'(A_142, k2_relat_1(A_142), C_143), C_143), A_142) | ~r2_hidden(C_143, k2_relat_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.31  tff(c_255, plain, (![A_144, C_145]: (r2_hidden('#skF_8'(A_144, k2_relat_1(A_144), C_145), k1_relat_1(A_144)) | ~r2_hidden(C_145, k2_relat_1(A_144)))), inference(resolution, [status(thm)], [c_234, c_6])).
% 2.30/1.31  tff(c_206, plain, (![A_1]: (m1_subset_1(A_1, '#skF_10') | ~r2_hidden(A_1, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_202, c_2])).
% 2.30/1.31  tff(c_261, plain, (![C_146]: (m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), C_146), '#skF_10') | ~r2_hidden(C_146, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_255, c_206])).
% 2.30/1.31  tff(c_42, plain, (![E_92]: (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11') | ~r2_hidden(k4_tarski(E_92, '#skF_14'), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_203, plain, (![E_92]: (~r2_hidden(k4_tarski(E_92, '#skF_14'), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.30/1.31  tff(c_238, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10') | ~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_234, c_203])).
% 2.30/1.31  tff(c_251, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_238])).
% 2.30/1.31  tff(c_264, plain, (~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_261, c_251])).
% 2.30/1.31  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_264])).
% 2.30/1.31  tff(c_269, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11')), inference(splitRight, [status(thm)], [c_42])).
% 2.30/1.31  tff(c_18, plain, (![C_38, A_23, D_41]: (r2_hidden(C_38, k2_relat_1(A_23)) | ~r2_hidden(k4_tarski(D_41, C_38), A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.31  tff(c_277, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_269, c_18])).
% 2.30/1.31  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_277])).
% 2.30/1.31  tff(c_283, plain, (![E_92]: (~r2_hidden(k4_tarski(E_92, '#skF_14'), '#skF_11') | ~m1_subset_1(E_92, '#skF_10'))), inference(splitRight, [status(thm)], [c_270])).
% 2.30/1.31  tff(c_334, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10') | ~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_330, c_283])).
% 2.30/1.31  tff(c_347, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_334])).
% 2.30/1.31  tff(c_360, plain, (~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_357, c_347])).
% 2.30/1.31  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_360])).
% 2.30/1.31  tff(c_366, plain, (~r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_50])).
% 2.30/1.31  tff(c_48, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11') | r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_373, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_366, c_48])).
% 2.30/1.31  tff(c_381, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_373, c_18])).
% 2.30/1.31  tff(c_392, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.30/1.31  tff(c_396, plain, (k2_relset_1('#skF_10', '#skF_9', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_34, c_392])).
% 2.30/1.31  tff(c_46, plain, (~r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_9', '#skF_11')) | r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_391, plain, (~r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_366, c_46])).
% 2.30/1.31  tff(c_397, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_391])).
% 2.30/1.31  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_381, c_397])).
% 2.30/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  Inference rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Ref     : 0
% 2.30/1.31  #Sup     : 68
% 2.30/1.31  #Fact    : 0
% 2.30/1.31  #Define  : 0
% 2.30/1.31  #Split   : 4
% 2.30/1.31  #Chain   : 0
% 2.30/1.31  #Close   : 0
% 2.30/1.31  
% 2.30/1.31  Ordering : KBO
% 2.30/1.31  
% 2.30/1.31  Simplification rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Subsume      : 1
% 2.30/1.31  #Demod        : 23
% 2.30/1.31  #Tautology    : 23
% 2.30/1.31  #SimpNegUnit  : 3
% 2.30/1.31  #BackRed      : 4
% 2.30/1.31  
% 2.30/1.31  #Partial instantiations: 0
% 2.30/1.31  #Strategies tried      : 1
% 2.30/1.31  
% 2.30/1.31  Timing (in seconds)
% 2.30/1.31  ----------------------
% 2.30/1.31  Preprocessing        : 0.31
% 2.30/1.31  Parsing              : 0.16
% 2.30/1.31  CNF conversion       : 0.03
% 2.30/1.31  Main loop            : 0.23
% 2.30/1.31  Inferencing          : 0.09
% 2.30/1.31  Reduction            : 0.07
% 2.30/1.32  Demodulation         : 0.05
% 2.30/1.32  BG Simplification    : 0.02
% 2.30/1.32  Subsumption          : 0.03
% 2.30/1.32  Abstraction          : 0.01
% 2.30/1.32  MUC search           : 0.00
% 2.30/1.32  Cooper               : 0.00
% 2.30/1.32  Total                : 0.58
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
