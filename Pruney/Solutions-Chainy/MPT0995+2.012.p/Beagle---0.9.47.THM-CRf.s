%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 129 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 322 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_13 > #skF_5 > #skF_7 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( ? [F] :
                  ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) )
             => r2_hidden(E,k7_relset_1(A,B,D,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_93,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_relset_1(A_76,B_77,C_78,D_79) = k9_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [D_79] : k7_relset_1('#skF_8','#skF_9','#skF_11',D_79) = k9_relat_1('#skF_11',D_79) ),
    inference(resolution,[status(thm)],[c_62,c_93])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_12',k7_relset_1('#skF_8','#skF_9','#skF_11','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_97,plain,(
    ~ r2_hidden('#skF_12',k9_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_52])).

tff(c_16,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,
    ( v1_relat_1('#skF_11')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_62,c_72])).

tff(c_78,plain,(
    v1_relat_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_75])).

tff(c_66,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    k1_funct_1('#skF_11','#skF_13') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_109,plain,(
    ! [A_86,C_87] :
      ( r2_hidden(k4_tarski(A_86,k1_funct_1(C_87,A_86)),C_87)
      | ~ r2_hidden(A_86,k1_relat_1(C_87))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11')
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_109])).

tff(c_123,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11')
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_66,c_118])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_13',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    v1_funct_2('#skF_11','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_217,plain,(
    ! [B_110,A_111,C_112] :
      ( k1_xboole_0 = B_110
      | k1_relset_1(A_111,B_110,C_112) = A_111
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_220,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_217])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_220])).

tff(c_224,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_11') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_223])).

tff(c_58,plain,(
    r2_hidden('#skF_13','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_326,plain,(
    ! [D_134,A_135,B_136,C_137] :
      ( r2_hidden(k4_tarski(D_134,'#skF_7'(A_135,B_136,C_137,D_134)),C_137)
      | ~ r2_hidden(D_134,B_136)
      | k1_relset_1(B_136,A_135,C_137) != B_136
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(B_136,A_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k1_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(C_19,D_22),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_426,plain,(
    ! [D_146,C_147,B_148,A_149] :
      ( r2_hidden(D_146,k1_relat_1(C_147))
      | ~ r2_hidden(D_146,B_148)
      | k1_relset_1(B_148,A_149,C_147) != B_148
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(B_148,A_149))) ) ),
    inference(resolution,[status(thm)],[c_326,c_6])).

tff(c_479,plain,(
    ! [C_152,A_153] :
      ( r2_hidden('#skF_13',k1_relat_1(C_152))
      | k1_relset_1('#skF_8',A_153,C_152) != '#skF_8'
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_153))) ) ),
    inference(resolution,[status(thm)],[c_58,c_426])).

tff(c_482,plain,
    ( r2_hidden('#skF_13',k1_relat_1('#skF_11'))
    | k1_relset_1('#skF_8','#skF_9','#skF_11') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_62,c_479])).

tff(c_485,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_482])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_485])).

tff(c_489,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_488,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_56,plain,(
    r2_hidden('#skF_13','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_677,plain,(
    ! [A_196,C_197,B_198,D_199] :
      ( r2_hidden(A_196,k9_relat_1(C_197,B_198))
      | ~ r2_hidden(D_199,B_198)
      | ~ r2_hidden(k4_tarski(D_199,A_196),C_197)
      | ~ r2_hidden(D_199,k1_relat_1(C_197))
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_720,plain,(
    ! [A_200,C_201] :
      ( r2_hidden(A_200,k9_relat_1(C_201,'#skF_10'))
      | ~ r2_hidden(k4_tarski('#skF_13',A_200),C_201)
      | ~ r2_hidden('#skF_13',k1_relat_1(C_201))
      | ~ v1_relat_1(C_201) ) ),
    inference(resolution,[status(thm)],[c_56,c_677])).

tff(c_723,plain,
    ( r2_hidden('#skF_12',k9_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_488,c_720])).

tff(c_734,plain,(
    r2_hidden('#skF_12',k9_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_489,c_723])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.54  
% 3.44/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.54  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_13 > #skF_5 > #skF_7 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12
% 3.44/1.54  
% 3.44/1.54  %Foreground sorts:
% 3.44/1.54  
% 3.44/1.54  
% 3.44/1.54  %Background operators:
% 3.44/1.54  
% 3.44/1.54  
% 3.44/1.54  %Foreground operators:
% 3.44/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.54  tff('#skF_11', type, '#skF_11': $i).
% 3.44/1.54  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.44/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.44/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.44/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.44/1.54  tff('#skF_10', type, '#skF_10': $i).
% 3.44/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.44/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.54  tff('#skF_13', type, '#skF_13': $i).
% 3.44/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.44/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.44/1.54  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.44/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.44/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.44/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.44/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.54  tff('#skF_12', type, '#skF_12': $i).
% 3.44/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.54  
% 3.44/1.55  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_2)).
% 3.44/1.55  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.44/1.55  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.44/1.55  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.44/1.55  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.44/1.55  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.44/1.55  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.44/1.55  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.44/1.55  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.44/1.55  tff(c_62, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_93, plain, (![A_76, B_77, C_78, D_79]: (k7_relset_1(A_76, B_77, C_78, D_79)=k9_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.44/1.55  tff(c_96, plain, (![D_79]: (k7_relset_1('#skF_8', '#skF_9', '#skF_11', D_79)=k9_relat_1('#skF_11', D_79))), inference(resolution, [status(thm)], [c_62, c_93])).
% 3.44/1.55  tff(c_52, plain, (~r2_hidden('#skF_12', k7_relset_1('#skF_8', '#skF_9', '#skF_11', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_97, plain, (~r2_hidden('#skF_12', k9_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_52])).
% 3.44/1.55  tff(c_16, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.55  tff(c_72, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.55  tff(c_75, plain, (v1_relat_1('#skF_11') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_62, c_72])).
% 3.44/1.55  tff(c_78, plain, (v1_relat_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_75])).
% 3.44/1.55  tff(c_66, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_54, plain, (k1_funct_1('#skF_11', '#skF_13')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_109, plain, (![A_86, C_87]: (r2_hidden(k4_tarski(A_86, k1_funct_1(C_87, A_86)), C_87) | ~r2_hidden(A_86, k1_relat_1(C_87)) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.55  tff(c_118, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11') | ~r2_hidden('#skF_13', k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_54, c_109])).
% 3.44/1.55  tff(c_123, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11') | ~r2_hidden('#skF_13', k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_66, c_118])).
% 3.44/1.55  tff(c_124, plain, (~r2_hidden('#skF_13', k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_123])).
% 3.44/1.55  tff(c_60, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_64, plain, (v1_funct_2('#skF_11', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_217, plain, (![B_110, A_111, C_112]: (k1_xboole_0=B_110 | k1_relset_1(A_111, B_110, C_112)=A_111 | ~v1_funct_2(C_112, A_111, B_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.44/1.55  tff(c_220, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_217])).
% 3.44/1.55  tff(c_223, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_220])).
% 3.44/1.55  tff(c_224, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_11')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_60, c_223])).
% 3.44/1.55  tff(c_58, plain, (r2_hidden('#skF_13', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.55  tff(c_326, plain, (![D_134, A_135, B_136, C_137]: (r2_hidden(k4_tarski(D_134, '#skF_7'(A_135, B_136, C_137, D_134)), C_137) | ~r2_hidden(D_134, B_136) | k1_relset_1(B_136, A_135, C_137)!=B_136 | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(B_136, A_135))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.55  tff(c_6, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k1_relat_1(A_4)) | ~r2_hidden(k4_tarski(C_19, D_22), A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.55  tff(c_426, plain, (![D_146, C_147, B_148, A_149]: (r2_hidden(D_146, k1_relat_1(C_147)) | ~r2_hidden(D_146, B_148) | k1_relset_1(B_148, A_149, C_147)!=B_148 | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(B_148, A_149))))), inference(resolution, [status(thm)], [c_326, c_6])).
% 3.44/1.55  tff(c_479, plain, (![C_152, A_153]: (r2_hidden('#skF_13', k1_relat_1(C_152)) | k1_relset_1('#skF_8', A_153, C_152)!='#skF_8' | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_153))))), inference(resolution, [status(thm)], [c_58, c_426])).
% 3.44/1.55  tff(c_482, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_11')) | k1_relset_1('#skF_8', '#skF_9', '#skF_11')!='#skF_8'), inference(resolution, [status(thm)], [c_62, c_479])).
% 3.44/1.55  tff(c_485, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_482])).
% 3.44/1.55  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_485])).
% 3.44/1.55  tff(c_489, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_123])).
% 3.44/1.56  tff(c_488, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_12'), '#skF_11')), inference(splitRight, [status(thm)], [c_123])).
% 3.44/1.56  tff(c_56, plain, (r2_hidden('#skF_13', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.44/1.56  tff(c_677, plain, (![A_196, C_197, B_198, D_199]: (r2_hidden(A_196, k9_relat_1(C_197, B_198)) | ~r2_hidden(D_199, B_198) | ~r2_hidden(k4_tarski(D_199, A_196), C_197) | ~r2_hidden(D_199, k1_relat_1(C_197)) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.56  tff(c_720, plain, (![A_200, C_201]: (r2_hidden(A_200, k9_relat_1(C_201, '#skF_10')) | ~r2_hidden(k4_tarski('#skF_13', A_200), C_201) | ~r2_hidden('#skF_13', k1_relat_1(C_201)) | ~v1_relat_1(C_201))), inference(resolution, [status(thm)], [c_56, c_677])).
% 3.44/1.56  tff(c_723, plain, (r2_hidden('#skF_12', k9_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_13', k1_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_488, c_720])).
% 3.44/1.56  tff(c_734, plain, (r2_hidden('#skF_12', k9_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_489, c_723])).
% 3.44/1.56  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_734])).
% 3.44/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.56  
% 3.44/1.56  Inference rules
% 3.44/1.56  ----------------------
% 3.44/1.56  #Ref     : 0
% 3.44/1.56  #Sup     : 157
% 3.44/1.56  #Fact    : 0
% 3.44/1.56  #Define  : 0
% 3.44/1.56  #Split   : 2
% 3.44/1.56  #Chain   : 0
% 3.44/1.56  #Close   : 0
% 3.44/1.56  
% 3.44/1.56  Ordering : KBO
% 3.44/1.56  
% 3.44/1.56  Simplification rules
% 3.44/1.56  ----------------------
% 3.44/1.56  #Subsume      : 5
% 3.44/1.56  #Demod        : 27
% 3.44/1.56  #Tautology    : 24
% 3.44/1.56  #SimpNegUnit  : 7
% 3.44/1.56  #BackRed      : 1
% 3.44/1.56  
% 3.44/1.56  #Partial instantiations: 0
% 3.44/1.56  #Strategies tried      : 1
% 3.44/1.56  
% 3.44/1.56  Timing (in seconds)
% 3.44/1.56  ----------------------
% 3.44/1.56  Preprocessing        : 0.35
% 3.44/1.56  Parsing              : 0.17
% 3.44/1.56  CNF conversion       : 0.03
% 3.44/1.56  Main loop            : 0.42
% 3.44/1.56  Inferencing          : 0.16
% 3.44/1.56  Reduction            : 0.11
% 3.44/1.56  Demodulation         : 0.08
% 3.44/1.56  BG Simplification    : 0.03
% 3.44/1.56  Subsumption          : 0.09
% 3.44/1.56  Abstraction          : 0.03
% 3.44/1.56  MUC search           : 0.00
% 3.44/1.56  Cooper               : 0.00
% 3.44/1.56  Total                : 0.81
% 3.44/1.56  Index Insertion      : 0.00
% 3.44/1.56  Index Deletion       : 0.00
% 3.44/1.56  Index Matching       : 0.00
% 3.44/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
