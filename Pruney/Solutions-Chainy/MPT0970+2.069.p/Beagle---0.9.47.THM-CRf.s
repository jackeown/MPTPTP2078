%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 146 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 362 expanded)
%              Number of equality atoms :   26 ( 104 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_36,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_75,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_79,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_30,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_80,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_30])).

tff(c_149,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_2'(A_81,B_82,C_83),B_82)
      | k2_relset_1(A_81,B_82,C_83) = B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_153,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_151])).

tff(c_154,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_153])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_40,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_7'(D_39),'#skF_4')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ! [D_39] :
      ( k1_funct_1('#skF_6','#skF_7'(D_39)) = D_39
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_452,plain,(
    ! [D_162,C_163,A_164,B_165] :
      ( r2_hidden(k1_funct_1(D_162,C_163),k2_relset_1(A_164,B_165,D_162))
      | k1_xboole_0 = B_165
      | ~ r2_hidden(C_163,A_164)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_2(D_162,A_164,B_165)
      | ~ v1_funct_1(D_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_464,plain,(
    ! [C_163] :
      ( r2_hidden(k1_funct_1('#skF_6',C_163),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_163,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_452])).

tff(c_473,plain,(
    ! [C_163] :
      ( r2_hidden(k1_funct_1('#skF_6',C_163),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_163,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_464])).

tff(c_476,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_497,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_2])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,(
    ~ r1_tarski('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_154,c_18])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_158])).

tff(c_509,plain,(
    ! [C_166] :
      ( r2_hidden(k1_funct_1('#skF_6',C_166),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_166,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_530,plain,(
    ! [D_168] :
      ( r2_hidden(D_168,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_168),'#skF_4')
      | ~ r2_hidden(D_168,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_509])).

tff(c_547,plain,(
    ! [D_173] :
      ( r2_hidden(D_173,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_173,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_530])).

tff(c_16,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden(k4_tarski('#skF_1'(A_7,B_8,C_9),A_7),C_9)
      | ~ r2_hidden(A_7,k9_relat_1(C_9,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [E_84,A_85,B_86,C_87] :
      ( ~ r2_hidden(k4_tarski(E_84,'#skF_2'(A_85,B_86,C_87)),C_87)
      | k2_relset_1(A_85,B_86,C_87) = B_86
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_283,plain,(
    ! [A_124,B_125,C_126,B_127] :
      ( k2_relset_1(A_124,B_125,C_126) = B_125
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ r2_hidden('#skF_2'(A_124,B_125,C_126),k9_relat_1(C_126,B_127))
      | ~ v1_relat_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_286,plain,(
    ! [A_124,B_125,A_13] :
      ( k2_relset_1(A_124,B_125,A_13) = B_125
      | ~ m1_subset_1(A_13,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ r2_hidden('#skF_2'(A_124,B_125,A_13),k2_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_283])).

tff(c_553,plain,(
    ! [A_124,B_125] :
      ( k2_relset_1(A_124,B_125,'#skF_6') = B_125
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden('#skF_2'(A_124,B_125,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_547,c_286])).

tff(c_619,plain,(
    ! [A_181,B_182] :
      ( k2_relset_1(A_181,B_182,'#skF_6') = B_182
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ r2_hidden('#skF_2'(A_181,B_182,'#skF_6'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_553])).

tff(c_622,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5'
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_619])).

tff(c_625,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_79,c_622])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:33:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.54  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.28/1.54  
% 3.28/1.54  %Foreground sorts:
% 3.28/1.54  
% 3.28/1.54  
% 3.28/1.54  %Background operators:
% 3.28/1.54  
% 3.28/1.54  
% 3.28/1.54  %Foreground operators:
% 3.28/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.54  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.28/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.28/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.28/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.28/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.28/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.28/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.54  
% 3.28/1.55  tff(f_103, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.28/1.55  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.28/1.55  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 3.28/1.55  tff(f_36, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.28/1.55  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.28/1.55  tff(f_84, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.28/1.55  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.28/1.55  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.28/1.55  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.28/1.55  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.28/1.55  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.28/1.55  tff(c_75, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.55  tff(c_79, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_75])).
% 3.28/1.55  tff(c_30, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.28/1.55  tff(c_80, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_30])).
% 3.28/1.55  tff(c_149, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_2'(A_81, B_82, C_83), B_82) | k2_relset_1(A_81, B_82, C_83)=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.28/1.55  tff(c_151, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_32, c_149])).
% 3.28/1.55  tff(c_153, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_151])).
% 3.28/1.55  tff(c_154, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_153])).
% 3.28/1.55  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.28/1.55  tff(c_68, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.55  tff(c_71, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_68])).
% 3.28/1.55  tff(c_74, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_71])).
% 3.28/1.55  tff(c_40, plain, (![D_39]: (r2_hidden('#skF_7'(D_39), '#skF_4') | ~r2_hidden(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.28/1.55  tff(c_38, plain, (![D_39]: (k1_funct_1('#skF_6', '#skF_7'(D_39))=D_39 | ~r2_hidden(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.28/1.55  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.28/1.55  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.28/1.55  tff(c_452, plain, (![D_162, C_163, A_164, B_165]: (r2_hidden(k1_funct_1(D_162, C_163), k2_relset_1(A_164, B_165, D_162)) | k1_xboole_0=B_165 | ~r2_hidden(C_163, A_164) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_2(D_162, A_164, B_165) | ~v1_funct_1(D_162))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.55  tff(c_464, plain, (![C_163]: (r2_hidden(k1_funct_1('#skF_6', C_163), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_163, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_452])).
% 3.28/1.55  tff(c_473, plain, (![C_163]: (r2_hidden(k1_funct_1('#skF_6', C_163), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_163, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_464])).
% 3.28/1.55  tff(c_476, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_473])).
% 3.28/1.55  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.55  tff(c_497, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_2])).
% 3.28/1.55  tff(c_18, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.55  tff(c_158, plain, (~r1_tarski('#skF_5', '#skF_2'('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_154, c_18])).
% 3.28/1.55  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_158])).
% 3.28/1.55  tff(c_509, plain, (![C_166]: (r2_hidden(k1_funct_1('#skF_6', C_166), k2_relat_1('#skF_6')) | ~r2_hidden(C_166, '#skF_4'))), inference(splitRight, [status(thm)], [c_473])).
% 3.28/1.55  tff(c_530, plain, (![D_168]: (r2_hidden(D_168, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_168), '#skF_4') | ~r2_hidden(D_168, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_509])).
% 3.28/1.55  tff(c_547, plain, (![D_173]: (r2_hidden(D_173, k2_relat_1('#skF_6')) | ~r2_hidden(D_173, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_530])).
% 3.28/1.55  tff(c_16, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.55  tff(c_12, plain, (![A_7, B_8, C_9]: (r2_hidden(k4_tarski('#skF_1'(A_7, B_8, C_9), A_7), C_9) | ~r2_hidden(A_7, k9_relat_1(C_9, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.55  tff(c_160, plain, (![E_84, A_85, B_86, C_87]: (~r2_hidden(k4_tarski(E_84, '#skF_2'(A_85, B_86, C_87)), C_87) | k2_relset_1(A_85, B_86, C_87)=B_86 | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.28/1.55  tff(c_283, plain, (![A_124, B_125, C_126, B_127]: (k2_relset_1(A_124, B_125, C_126)=B_125 | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~r2_hidden('#skF_2'(A_124, B_125, C_126), k9_relat_1(C_126, B_127)) | ~v1_relat_1(C_126))), inference(resolution, [status(thm)], [c_12, c_160])).
% 3.28/1.55  tff(c_286, plain, (![A_124, B_125, A_13]: (k2_relset_1(A_124, B_125, A_13)=B_125 | ~m1_subset_1(A_13, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~r2_hidden('#skF_2'(A_124, B_125, A_13), k2_relat_1(A_13)) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_283])).
% 3.28/1.55  tff(c_553, plain, (![A_124, B_125]: (k2_relset_1(A_124, B_125, '#skF_6')=B_125 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_2'(A_124, B_125, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_547, c_286])).
% 3.28/1.55  tff(c_619, plain, (![A_181, B_182]: (k2_relset_1(A_181, B_182, '#skF_6')=B_182 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~r2_hidden('#skF_2'(A_181, B_182, '#skF_6'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_553])).
% 3.28/1.55  tff(c_622, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5' | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_32, c_619])).
% 3.28/1.55  tff(c_625, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_79, c_622])).
% 3.28/1.55  tff(c_627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_625])).
% 3.28/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.55  
% 3.28/1.55  Inference rules
% 3.28/1.55  ----------------------
% 3.28/1.55  #Ref     : 0
% 3.28/1.55  #Sup     : 116
% 3.28/1.55  #Fact    : 0
% 3.28/1.55  #Define  : 0
% 3.28/1.55  #Split   : 6
% 3.28/1.55  #Chain   : 0
% 3.28/1.55  #Close   : 0
% 3.28/1.55  
% 3.28/1.55  Ordering : KBO
% 3.28/1.55  
% 3.28/1.55  Simplification rules
% 3.28/1.55  ----------------------
% 3.28/1.55  #Subsume      : 23
% 3.28/1.55  #Demod        : 55
% 3.28/1.55  #Tautology    : 8
% 3.28/1.55  #SimpNegUnit  : 7
% 3.28/1.55  #BackRed      : 27
% 3.28/1.55  
% 3.28/1.55  #Partial instantiations: 0
% 3.39/1.55  #Strategies tried      : 1
% 3.39/1.55  
% 3.39/1.55  Timing (in seconds)
% 3.39/1.55  ----------------------
% 3.39/1.56  Preprocessing        : 0.33
% 3.39/1.56  Parsing              : 0.18
% 3.39/1.56  CNF conversion       : 0.02
% 3.39/1.56  Main loop            : 0.40
% 3.39/1.56  Inferencing          : 0.14
% 3.39/1.56  Reduction            : 0.09
% 3.39/1.56  Demodulation         : 0.07
% 3.39/1.56  BG Simplification    : 0.02
% 3.39/1.56  Subsumption          : 0.12
% 3.39/1.56  Abstraction          : 0.02
% 3.39/1.56  MUC search           : 0.00
% 3.39/1.56  Cooper               : 0.00
% 3.39/1.56  Total                : 0.77
% 3.39/1.56  Index Insertion      : 0.00
% 3.39/1.56  Index Deletion       : 0.00
% 3.39/1.56  Index Matching       : 0.00
% 3.39/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
