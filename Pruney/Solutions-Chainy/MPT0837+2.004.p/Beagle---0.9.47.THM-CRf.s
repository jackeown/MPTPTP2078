%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:05 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 167 expanded)
%              Number of leaves         :   39 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 340 expanded)
%              Number of equality atoms :    7 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_14 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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

tff(f_90,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_71,plain,(
    ! [C_101,A_102,B_103] :
      ( v1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_90,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,(
    v4_relat_1('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_384,plain,(
    ! [A_205,B_206,C_207] :
      ( k2_relset_1(A_205,B_206,C_207) = k2_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_393,plain,(
    k2_relset_1('#skF_10','#skF_9','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_44,c_384])).

tff(c_60,plain,
    ( m1_subset_1('#skF_13','#skF_10')
    | r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_87,plain,(
    r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_395,plain,(
    r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_87])).

tff(c_737,plain,(
    ! [A_276,C_277] :
      ( r2_hidden(k4_tarski('#skF_8'(A_276,k2_relat_1(A_276),C_277),C_277),A_276)
      | ~ r2_hidden(C_277,k2_relat_1(A_276)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_760,plain,(
    ! [A_278,C_279] :
      ( r2_hidden('#skF_8'(A_278,k2_relat_1(A_278),C_279),k1_relat_1(A_278))
      | ~ r2_hidden(C_279,k2_relat_1(A_278)) ) ),
    inference(resolution,[status(thm)],[c_737,c_14])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_366,plain,(
    ! [A_188,C_189,B_190] :
      ( m1_subset_1(A_188,C_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(C_189))
      | ~ r2_hidden(A_188,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_371,plain,(
    ! [A_188,B_2,A_1] :
      ( m1_subset_1(A_188,B_2)
      | ~ r2_hidden(A_188,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_366])).

tff(c_797,plain,(
    ! [A_292,C_293,B_294] :
      ( m1_subset_1('#skF_8'(A_292,k2_relat_1(A_292),C_293),B_294)
      | ~ r1_tarski(k1_relat_1(A_292),B_294)
      | ~ r2_hidden(C_293,k2_relat_1(A_292)) ) ),
    inference(resolution,[status(thm)],[c_760,c_371])).

tff(c_417,plain,(
    ! [A_213,C_214] :
      ( r2_hidden(k4_tarski('#skF_8'(A_213,k2_relat_1(A_213),C_214),C_214),A_213)
      | ~ r2_hidden(C_214,k2_relat_1(A_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_436,plain,(
    ! [A_215,C_216] :
      ( r2_hidden('#skF_8'(A_215,k2_relat_1(A_215),C_216),k1_relat_1(A_215))
      | ~ r2_hidden(C_216,k2_relat_1(A_215)) ) ),
    inference(resolution,[status(thm)],[c_417,c_14])).

tff(c_552,plain,(
    ! [A_249,C_250,B_251] :
      ( m1_subset_1('#skF_8'(A_249,k2_relat_1(A_249),C_250),B_251)
      | ~ r1_tarski(k1_relat_1(A_249),B_251)
      | ~ r2_hidden(C_250,k2_relat_1(A_249)) ) ),
    inference(resolution,[status(thm)],[c_436,c_371])).

tff(c_52,plain,(
    ! [E_96] :
      ( r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11')
      | ~ r2_hidden(k4_tarski(E_96,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_400,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski(E_96,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10') ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_421,plain,
    ( ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10')
    | ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_417,c_400])).

tff(c_432,plain,(
    ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_421])).

tff(c_555,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_11'),'#skF_10')
    | ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_552,c_432])).

tff(c_581,plain,(
    ~ r1_tarski(k1_relat_1('#skF_11'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_555])).

tff(c_590,plain,
    ( ~ v4_relat_1('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_581])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_99,c_590])).

tff(c_595,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_26,plain,(
    ! [C_42,A_27,D_45] :
      ( r2_hidden(C_42,k2_relat_1(A_27))
      | ~ r2_hidden(k4_tarski(D_45,C_42),A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_606,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_595,c_26])).

tff(c_50,plain,(
    ! [E_96] :
      ( ~ r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_9','#skF_11'))
      | ~ r2_hidden(k4_tarski(E_96,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_617,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski(E_96,'#skF_14'),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_393,c_50])).

tff(c_744,plain,
    ( ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10')
    | ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_737,c_617])).

tff(c_756,plain,(
    ~ m1_subset_1('#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_14'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_744])).

tff(c_800,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_11'),'#skF_10')
    | ~ r2_hidden('#skF_14',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_797,c_756])).

tff(c_826,plain,(
    ~ r1_tarski(k1_relat_1('#skF_11'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_800])).

tff(c_865,plain,
    ( ~ v4_relat_1('#skF_11','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_826])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_99,c_865])).

tff(c_871,plain,(
    ~ r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11')
    | r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_935,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_871,c_58])).

tff(c_943,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_935,c_26])).

tff(c_996,plain,(
    ! [A_330,B_331,C_332] :
      ( k2_relset_1(A_330,B_331,C_332) = k2_relat_1(C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1010,plain,(
    k2_relset_1('#skF_10','#skF_9','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_44,c_996])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_9','#skF_11'))
    | r2_hidden('#skF_14',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_945,plain,(
    ~ r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_871,c_56])).

tff(c_1011,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_945])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_1011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.53  
% 3.11/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.53  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_14 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_11', type, '#skF_11': $i).
% 3.11/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.11/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_10', type, '#skF_10': $i).
% 3.11/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.53  tff('#skF_14', type, '#skF_14': $i).
% 3.11/1.53  tff('#skF_13', type, '#skF_13': $i).
% 3.11/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.11/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.11/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.11/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.53  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.11/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.53  tff('#skF_12', type, '#skF_12': $i).
% 3.11/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.53  
% 3.33/1.55  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 3.33/1.55  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.55  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.55  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.33/1.55  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.33/1.55  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.33/1.55  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.33/1.55  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.33/1.55  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.33/1.55  tff(c_44, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.55  tff(c_71, plain, (![C_101, A_102, B_103]: (v1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.55  tff(c_80, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_44, c_71])).
% 3.33/1.55  tff(c_90, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.55  tff(c_99, plain, (v4_relat_1('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_44, c_90])).
% 3.33/1.55  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.55  tff(c_384, plain, (![A_205, B_206, C_207]: (k2_relset_1(A_205, B_206, C_207)=k2_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.33/1.55  tff(c_393, plain, (k2_relset_1('#skF_10', '#skF_9', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_44, c_384])).
% 3.33/1.55  tff(c_60, plain, (m1_subset_1('#skF_13', '#skF_10') | r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.55  tff(c_87, plain, (r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.33/1.55  tff(c_395, plain, (r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_87])).
% 3.33/1.55  tff(c_737, plain, (![A_276, C_277]: (r2_hidden(k4_tarski('#skF_8'(A_276, k2_relat_1(A_276), C_277), C_277), A_276) | ~r2_hidden(C_277, k2_relat_1(A_276)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.55  tff(c_14, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.33/1.55  tff(c_760, plain, (![A_278, C_279]: (r2_hidden('#skF_8'(A_278, k2_relat_1(A_278), C_279), k1_relat_1(A_278)) | ~r2_hidden(C_279, k2_relat_1(A_278)))), inference(resolution, [status(thm)], [c_737, c_14])).
% 3.33/1.55  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.55  tff(c_366, plain, (![A_188, C_189, B_190]: (m1_subset_1(A_188, C_189) | ~m1_subset_1(B_190, k1_zfmisc_1(C_189)) | ~r2_hidden(A_188, B_190))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.55  tff(c_371, plain, (![A_188, B_2, A_1]: (m1_subset_1(A_188, B_2) | ~r2_hidden(A_188, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_366])).
% 3.33/1.55  tff(c_797, plain, (![A_292, C_293, B_294]: (m1_subset_1('#skF_8'(A_292, k2_relat_1(A_292), C_293), B_294) | ~r1_tarski(k1_relat_1(A_292), B_294) | ~r2_hidden(C_293, k2_relat_1(A_292)))), inference(resolution, [status(thm)], [c_760, c_371])).
% 3.33/1.55  tff(c_417, plain, (![A_213, C_214]: (r2_hidden(k4_tarski('#skF_8'(A_213, k2_relat_1(A_213), C_214), C_214), A_213) | ~r2_hidden(C_214, k2_relat_1(A_213)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.55  tff(c_436, plain, (![A_215, C_216]: (r2_hidden('#skF_8'(A_215, k2_relat_1(A_215), C_216), k1_relat_1(A_215)) | ~r2_hidden(C_216, k2_relat_1(A_215)))), inference(resolution, [status(thm)], [c_417, c_14])).
% 3.33/1.55  tff(c_552, plain, (![A_249, C_250, B_251]: (m1_subset_1('#skF_8'(A_249, k2_relat_1(A_249), C_250), B_251) | ~r1_tarski(k1_relat_1(A_249), B_251) | ~r2_hidden(C_250, k2_relat_1(A_249)))), inference(resolution, [status(thm)], [c_436, c_371])).
% 3.33/1.55  tff(c_52, plain, (![E_96]: (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11') | ~r2_hidden(k4_tarski(E_96, '#skF_14'), '#skF_11') | ~m1_subset_1(E_96, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.55  tff(c_400, plain, (![E_96]: (~r2_hidden(k4_tarski(E_96, '#skF_14'), '#skF_11') | ~m1_subset_1(E_96, '#skF_10'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.33/1.55  tff(c_421, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10') | ~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_417, c_400])).
% 3.33/1.55  tff(c_432, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_421])).
% 3.33/1.55  tff(c_555, plain, (~r1_tarski(k1_relat_1('#skF_11'), '#skF_10') | ~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_552, c_432])).
% 3.33/1.55  tff(c_581, plain, (~r1_tarski(k1_relat_1('#skF_11'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_555])).
% 3.33/1.55  tff(c_590, plain, (~v4_relat_1('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_10, c_581])).
% 3.33/1.55  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_99, c_590])).
% 3.33/1.55  tff(c_595, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11')), inference(splitRight, [status(thm)], [c_52])).
% 3.33/1.55  tff(c_26, plain, (![C_42, A_27, D_45]: (r2_hidden(C_42, k2_relat_1(A_27)) | ~r2_hidden(k4_tarski(D_45, C_42), A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.55  tff(c_606, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_595, c_26])).
% 3.33/1.55  tff(c_50, plain, (![E_96]: (~r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_9', '#skF_11')) | ~r2_hidden(k4_tarski(E_96, '#skF_14'), '#skF_11') | ~m1_subset_1(E_96, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.55  tff(c_617, plain, (![E_96]: (~r2_hidden(k4_tarski(E_96, '#skF_14'), '#skF_11') | ~m1_subset_1(E_96, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_393, c_50])).
% 3.33/1.55  tff(c_744, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10') | ~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_737, c_617])).
% 3.33/1.55  tff(c_756, plain, (~m1_subset_1('#skF_8'('#skF_11', k2_relat_1('#skF_11'), '#skF_14'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_744])).
% 3.33/1.55  tff(c_800, plain, (~r1_tarski(k1_relat_1('#skF_11'), '#skF_10') | ~r2_hidden('#skF_14', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_797, c_756])).
% 3.33/1.55  tff(c_826, plain, (~r1_tarski(k1_relat_1('#skF_11'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_800])).
% 3.33/1.55  tff(c_865, plain, (~v4_relat_1('#skF_11', '#skF_10') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_10, c_826])).
% 3.33/1.55  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_99, c_865])).
% 3.33/1.55  tff(c_871, plain, (~r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_60])).
% 3.33/1.55  tff(c_58, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11') | r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.55  tff(c_935, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_871, c_58])).
% 3.33/1.55  tff(c_943, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_935, c_26])).
% 3.33/1.55  tff(c_996, plain, (![A_330, B_331, C_332]: (k2_relset_1(A_330, B_331, C_332)=k2_relat_1(C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.33/1.55  tff(c_1010, plain, (k2_relset_1('#skF_10', '#skF_9', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_44, c_996])).
% 3.33/1.55  tff(c_56, plain, (~r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_9', '#skF_11')) | r2_hidden('#skF_14', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.55  tff(c_945, plain, (~r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_871, c_56])).
% 3.33/1.55  tff(c_1011, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_945])).
% 3.33/1.55  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_943, c_1011])).
% 3.33/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.55  
% 3.33/1.55  Inference rules
% 3.33/1.55  ----------------------
% 3.33/1.55  #Ref     : 0
% 3.33/1.55  #Sup     : 192
% 3.33/1.55  #Fact    : 0
% 3.33/1.55  #Define  : 0
% 3.33/1.55  #Split   : 4
% 3.33/1.55  #Chain   : 0
% 3.33/1.55  #Close   : 0
% 3.33/1.55  
% 3.33/1.55  Ordering : KBO
% 3.33/1.55  
% 3.33/1.55  Simplification rules
% 3.33/1.55  ----------------------
% 3.33/1.55  #Subsume      : 13
% 3.33/1.55  #Demod        : 40
% 3.33/1.55  #Tautology    : 29
% 3.33/1.55  #SimpNegUnit  : 2
% 3.33/1.55  #BackRed      : 6
% 3.33/1.55  
% 3.33/1.55  #Partial instantiations: 0
% 3.33/1.55  #Strategies tried      : 1
% 3.33/1.55  
% 3.33/1.55  Timing (in seconds)
% 3.33/1.55  ----------------------
% 3.33/1.55  Preprocessing        : 0.35
% 3.33/1.55  Parsing              : 0.18
% 3.33/1.55  CNF conversion       : 0.03
% 3.33/1.55  Main loop            : 0.42
% 3.33/1.55  Inferencing          : 0.17
% 3.33/1.55  Reduction            : 0.11
% 3.33/1.55  Demodulation         : 0.07
% 3.33/1.55  BG Simplification    : 0.02
% 3.33/1.55  Subsumption          : 0.07
% 3.33/1.55  Abstraction          : 0.02
% 3.33/1.55  MUC search           : 0.00
% 3.33/1.55  Cooper               : 0.00
% 3.33/1.55  Total                : 0.81
% 3.33/1.55  Index Insertion      : 0.00
% 3.33/1.55  Index Deletion       : 0.00
% 3.33/1.55  Index Matching       : 0.00
% 3.33/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
