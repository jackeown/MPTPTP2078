%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 129 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 282 expanded)
%              Number of equality atoms :   30 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_95,plain,(
    ! [C_60,B_61,A_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(B_61,A_62)))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_105,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_84,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_151,plain,(
    ! [A_80,C_81] :
      ( r2_hidden(k4_tarski('#skF_5'(A_80,k2_relat_1(A_80),C_81),C_81),A_80)
      | ~ r2_hidden(C_81,k2_relat_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [C_28,A_26,B_27] :
      ( k1_funct_1(C_28,A_26) = B_27
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_167,plain,(
    ! [A_80,C_81] :
      ( k1_funct_1(A_80,'#skF_5'(A_80,k2_relat_1(A_80),C_81)) = C_81
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80)
      | ~ r2_hidden(C_81,k2_relat_1(A_80)) ) ),
    inference(resolution,[status(thm)],[c_151,c_24])).

tff(c_54,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_108,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_117,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_391,plain,(
    ! [B_123,A_124,C_125] :
      ( k1_xboole_0 = B_123
      | k1_relset_1(A_124,B_123,C_125) = A_124
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_398,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_391])).

tff(c_402,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_117,c_398])).

tff(c_403,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_26,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3954,plain,(
    ! [A_176,C_177] :
      ( r2_hidden('#skF_5'(A_176,k2_relat_1(A_176),C_177),k1_relat_1(A_176))
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176)
      | ~ r2_hidden(C_177,k2_relat_1(A_176)) ) ),
    inference(resolution,[status(thm)],[c_151,c_26])).

tff(c_3993,plain,(
    ! [C_177] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_177),'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_177,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_3954])).

tff(c_4306,plain,(
    ! [C_190] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_190),'#skF_7')
      | ~ r2_hidden(C_190,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56,c_3993])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4826,plain,(
    ! [C_212] :
      ( m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_212),'#skF_7')
      | ~ r2_hidden(C_212,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_4306,c_8])).

tff(c_48,plain,(
    ! [E_46] :
      ( k1_funct_1('#skF_9',E_46) != '#skF_6'
      | ~ m1_subset_1(E_46,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5262,plain,(
    ! [C_223] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_223)) != '#skF_6'
      | ~ r2_hidden(C_223,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_4826,c_48])).

tff(c_5266,plain,(
    ! [C_81] :
      ( C_81 != '#skF_6'
      | ~ r2_hidden(C_81,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_81,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_5262])).

tff(c_5269,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56,c_5266])).

tff(c_122,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_122])).

tff(c_50,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_135,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_50])).

tff(c_5271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5269,c_135])).

tff(c_5272,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5279,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5272,c_6])).

tff(c_5281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_5279])).

tff(c_5282,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_5285,plain,(
    ! [A_226,B_227,C_228] :
      ( k2_relset_1(A_226,B_227,C_228) = k2_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5294,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_5285])).

tff(c_5297,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5294,c_50])).

tff(c_5328,plain,(
    ! [A_239,C_240] :
      ( r2_hidden(k4_tarski('#skF_5'(A_239,k2_relat_1(A_239),C_240),C_240),A_239)
      | ~ r2_hidden(C_240,k2_relat_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5349,plain,(
    ! [A_241,C_242] :
      ( ~ v1_xboole_0(A_241)
      | ~ r2_hidden(C_242,k2_relat_1(A_241)) ) ),
    inference(resolution,[status(thm)],[c_5328,c_2])).

tff(c_5356,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_5297,c_5349])).

tff(c_5365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5282,c_5356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.04  
% 5.32/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.04  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 5.32/2.04  
% 5.32/2.04  %Foreground sorts:
% 5.32/2.04  
% 5.32/2.04  
% 5.32/2.04  %Background operators:
% 5.32/2.04  
% 5.32/2.04  
% 5.32/2.04  %Foreground operators:
% 5.32/2.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.32/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.32/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/2.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.32/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.32/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.32/2.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.32/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.32/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.32/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.32/2.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.32/2.04  tff('#skF_9', type, '#skF_9': $i).
% 5.32/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.32/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.04  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.32/2.04  tff('#skF_8', type, '#skF_8': $i).
% 5.32/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.32/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.32/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.32/2.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.32/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.04  
% 5.32/2.06  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 5.32/2.06  tff(f_65, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.32/2.06  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.32/2.06  tff(f_44, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 5.32/2.06  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.32/2.06  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.32/2.06  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.32/2.06  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.32/2.06  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.32/2.06  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.32/2.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.32/2.06  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.32/2.06  tff(c_95, plain, (![C_60, B_61, A_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(B_61, A_62))) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.32/2.06  tff(c_104, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_52, c_95])).
% 5.32/2.06  tff(c_105, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_104])).
% 5.32/2.06  tff(c_84, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.32/2.06  tff(c_93, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_84])).
% 5.32/2.06  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.32/2.06  tff(c_151, plain, (![A_80, C_81]: (r2_hidden(k4_tarski('#skF_5'(A_80, k2_relat_1(A_80), C_81), C_81), A_80) | ~r2_hidden(C_81, k2_relat_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.32/2.06  tff(c_24, plain, (![C_28, A_26, B_27]: (k1_funct_1(C_28, A_26)=B_27 | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.32/2.06  tff(c_167, plain, (![A_80, C_81]: (k1_funct_1(A_80, '#skF_5'(A_80, k2_relat_1(A_80), C_81))=C_81 | ~v1_funct_1(A_80) | ~v1_relat_1(A_80) | ~r2_hidden(C_81, k2_relat_1(A_80)))), inference(resolution, [status(thm)], [c_151, c_24])).
% 5.32/2.06  tff(c_54, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.32/2.06  tff(c_108, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.32/2.06  tff(c_117, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_108])).
% 5.32/2.06  tff(c_391, plain, (![B_123, A_124, C_125]: (k1_xboole_0=B_123 | k1_relset_1(A_124, B_123, C_125)=A_124 | ~v1_funct_2(C_125, A_124, B_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.32/2.06  tff(c_398, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_391])).
% 5.32/2.06  tff(c_402, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_117, c_398])).
% 5.32/2.06  tff(c_403, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_402])).
% 5.32/2.06  tff(c_26, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.32/2.06  tff(c_3954, plain, (![A_176, C_177]: (r2_hidden('#skF_5'(A_176, k2_relat_1(A_176), C_177), k1_relat_1(A_176)) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176) | ~r2_hidden(C_177, k2_relat_1(A_176)))), inference(resolution, [status(thm)], [c_151, c_26])).
% 5.32/2.06  tff(c_3993, plain, (![C_177]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_177), '#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_177, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_403, c_3954])).
% 5.32/2.06  tff(c_4306, plain, (![C_190]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_190), '#skF_7') | ~r2_hidden(C_190, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56, c_3993])).
% 5.32/2.06  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.32/2.06  tff(c_4826, plain, (![C_212]: (m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_212), '#skF_7') | ~r2_hidden(C_212, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_4306, c_8])).
% 5.32/2.06  tff(c_48, plain, (![E_46]: (k1_funct_1('#skF_9', E_46)!='#skF_6' | ~m1_subset_1(E_46, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.32/2.06  tff(c_5262, plain, (![C_223]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_223))!='#skF_6' | ~r2_hidden(C_223, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_4826, c_48])).
% 5.32/2.06  tff(c_5266, plain, (![C_81]: (C_81!='#skF_6' | ~r2_hidden(C_81, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_81, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_5262])).
% 5.32/2.06  tff(c_5269, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56, c_5266])).
% 5.32/2.06  tff(c_122, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.32/2.06  tff(c_131, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_122])).
% 5.32/2.06  tff(c_50, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.32/2.06  tff(c_135, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_50])).
% 5.32/2.06  tff(c_5271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5269, c_135])).
% 5.32/2.06  tff(c_5272, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_402])).
% 5.32/2.06  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.32/2.06  tff(c_5279, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5272, c_6])).
% 5.32/2.06  tff(c_5281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_5279])).
% 5.32/2.06  tff(c_5282, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_104])).
% 5.32/2.06  tff(c_5285, plain, (![A_226, B_227, C_228]: (k2_relset_1(A_226, B_227, C_228)=k2_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.32/2.06  tff(c_5294, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_5285])).
% 5.32/2.06  tff(c_5297, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5294, c_50])).
% 5.32/2.06  tff(c_5328, plain, (![A_239, C_240]: (r2_hidden(k4_tarski('#skF_5'(A_239, k2_relat_1(A_239), C_240), C_240), A_239) | ~r2_hidden(C_240, k2_relat_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.32/2.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.06  tff(c_5349, plain, (![A_241, C_242]: (~v1_xboole_0(A_241) | ~r2_hidden(C_242, k2_relat_1(A_241)))), inference(resolution, [status(thm)], [c_5328, c_2])).
% 5.32/2.06  tff(c_5356, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_5297, c_5349])).
% 5.32/2.06  tff(c_5365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5282, c_5356])).
% 5.32/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.06  
% 5.32/2.06  Inference rules
% 5.32/2.06  ----------------------
% 5.32/2.06  #Ref     : 0
% 5.32/2.06  #Sup     : 1349
% 5.32/2.06  #Fact    : 0
% 5.32/2.06  #Define  : 0
% 5.32/2.06  #Split   : 7
% 5.32/2.06  #Chain   : 0
% 5.32/2.06  #Close   : 0
% 5.32/2.06  
% 5.32/2.06  Ordering : KBO
% 5.32/2.06  
% 5.32/2.06  Simplification rules
% 5.32/2.06  ----------------------
% 5.32/2.06  #Subsume      : 491
% 5.32/2.06  #Demod        : 1192
% 5.32/2.06  #Tautology    : 319
% 5.32/2.06  #SimpNegUnit  : 23
% 5.32/2.06  #BackRed      : 14
% 5.32/2.06  
% 5.32/2.06  #Partial instantiations: 0
% 5.32/2.06  #Strategies tried      : 1
% 5.32/2.06  
% 5.32/2.06  Timing (in seconds)
% 5.32/2.06  ----------------------
% 5.32/2.06  Preprocessing        : 0.33
% 5.32/2.06  Parsing              : 0.17
% 5.32/2.06  CNF conversion       : 0.02
% 5.32/2.06  Main loop            : 0.96
% 5.32/2.06  Inferencing          : 0.28
% 5.32/2.06  Reduction            : 0.26
% 5.32/2.06  Demodulation         : 0.19
% 5.32/2.06  BG Simplification    : 0.04
% 5.32/2.06  Subsumption          : 0.30
% 5.32/2.06  Abstraction          : 0.06
% 5.32/2.06  MUC search           : 0.00
% 5.32/2.06  Cooper               : 0.00
% 5.32/2.06  Total                : 1.32
% 5.32/2.06  Index Insertion      : 0.00
% 5.32/2.06  Index Deletion       : 0.00
% 5.32/2.06  Index Matching       : 0.00
% 5.32/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
