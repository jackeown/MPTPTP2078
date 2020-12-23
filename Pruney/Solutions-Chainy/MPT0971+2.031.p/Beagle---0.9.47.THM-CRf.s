%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 137 expanded)
%              Number of leaves         :   39 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 292 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_151,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_155,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_151])).

tff(c_54,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_158,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_81])).

tff(c_175,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1(k2_relset_1(A_102,B_103,C_104),k1_zfmisc_1(B_103))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_200,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_175])).

tff(c_208,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_200])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,(
    ! [A_87,A_88] :
      ( r2_hidden('#skF_1'(A_87),A_88)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(A_88))
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_126,plain,(
    ! [A_88,A_87] :
      ( ~ v1_xboole_0(A_88)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(A_88))
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_211,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_208,c_126])).

tff(c_217,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_211])).

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_101,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_98])).

tff(c_60,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16,plain,(
    ! [A_15,C_51] :
      ( k1_funct_1(A_15,'#skF_5'(A_15,k2_relat_1(A_15),C_51)) = C_51
      | ~ r2_hidden(C_51,k2_relat_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_139,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_139])).

tff(c_423,plain,(
    ! [B_156,A_157,C_158] :
      ( k1_xboole_0 = B_156
      | k1_relset_1(A_157,B_156,C_158) = A_157
      | ~ v1_funct_2(C_158,A_157,B_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_430,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_423])).

tff(c_434,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_143,c_430])).

tff(c_435,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_18,plain,(
    ! [A_15,C_51] :
      ( r2_hidden('#skF_5'(A_15,k2_relat_1(A_15),C_51),k1_relat_1(A_15))
      | ~ r2_hidden(C_51,k2_relat_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_444,plain,(
    ! [C_51] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_51),'#skF_6')
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_18])).

tff(c_477,plain,(
    ! [C_162] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_162),'#skF_6')
      | ~ r2_hidden(C_162,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_60,c_444])).

tff(c_52,plain,(
    ! [E_70] :
      ( k1_funct_1('#skF_9',E_70) != '#skF_8'
      | ~ r2_hidden(E_70,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_494,plain,(
    ! [C_164] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_164)) != '#skF_8'
      | ~ r2_hidden(C_164,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_477,c_52])).

tff(c_498,plain,(
    ! [C_51] :
      ( C_51 != '#skF_8'
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_494])).

tff(c_501,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_60,c_498])).

tff(c_159,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_54])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_159])).

tff(c_504,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [B_77,A_78] :
      ( ~ r1_tarski(B_77,A_78)
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,'#skF_1'(A_80))
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_93,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_513,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_93])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.53  
% 3.00/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.54  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 3.00/1.54  
% 3.00/1.54  %Foreground sorts:
% 3.00/1.54  
% 3.00/1.54  
% 3.00/1.54  %Background operators:
% 3.00/1.54  
% 3.00/1.54  
% 3.00/1.54  %Foreground operators:
% 3.00/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.00/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.00/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.00/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.00/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.00/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.00/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.00/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.00/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.54  
% 3.07/1.55  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 3.07/1.55  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.07/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.07/1.55  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.07/1.55  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.07/1.55  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.07/1.55  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.07/1.55  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.07/1.55  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.07/1.55  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.07/1.55  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.55  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.55  tff(c_56, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.07/1.55  tff(c_151, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.07/1.55  tff(c_155, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_151])).
% 3.07/1.55  tff(c_54, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.07/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.55  tff(c_81, plain, (~v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 3.07/1.55  tff(c_158, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_81])).
% 3.07/1.55  tff(c_175, plain, (![A_102, B_103, C_104]: (m1_subset_1(k2_relset_1(A_102, B_103, C_104), k1_zfmisc_1(B_103)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.55  tff(c_200, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_155, c_175])).
% 3.07/1.55  tff(c_208, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_200])).
% 3.07/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.55  tff(c_102, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.55  tff(c_110, plain, (![A_87, A_88]: (r2_hidden('#skF_1'(A_87), A_88) | ~m1_subset_1(A_87, k1_zfmisc_1(A_88)) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_4, c_102])).
% 3.07/1.55  tff(c_126, plain, (![A_88, A_87]: (~v1_xboole_0(A_88) | ~m1_subset_1(A_87, k1_zfmisc_1(A_88)) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_110, c_2])).
% 3.07/1.55  tff(c_211, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_208, c_126])).
% 3.07/1.55  tff(c_217, plain, (~v1_xboole_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_158, c_211])).
% 3.07/1.55  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.55  tff(c_95, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.55  tff(c_98, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_56, c_95])).
% 3.07/1.55  tff(c_101, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_98])).
% 3.07/1.55  tff(c_60, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.07/1.55  tff(c_16, plain, (![A_15, C_51]: (k1_funct_1(A_15, '#skF_5'(A_15, k2_relat_1(A_15), C_51))=C_51 | ~r2_hidden(C_51, k2_relat_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.55  tff(c_58, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.07/1.55  tff(c_139, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.07/1.55  tff(c_143, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_139])).
% 3.07/1.55  tff(c_423, plain, (![B_156, A_157, C_158]: (k1_xboole_0=B_156 | k1_relset_1(A_157, B_156, C_158)=A_157 | ~v1_funct_2(C_158, A_157, B_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.55  tff(c_430, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_423])).
% 3.07/1.55  tff(c_434, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_143, c_430])).
% 3.07/1.55  tff(c_435, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_434])).
% 3.07/1.55  tff(c_18, plain, (![A_15, C_51]: (r2_hidden('#skF_5'(A_15, k2_relat_1(A_15), C_51), k1_relat_1(A_15)) | ~r2_hidden(C_51, k2_relat_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.55  tff(c_444, plain, (![C_51]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_51), '#skF_6') | ~r2_hidden(C_51, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_18])).
% 3.07/1.55  tff(c_477, plain, (![C_162]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_162), '#skF_6') | ~r2_hidden(C_162, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_60, c_444])).
% 3.07/1.55  tff(c_52, plain, (![E_70]: (k1_funct_1('#skF_9', E_70)!='#skF_8' | ~r2_hidden(E_70, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.07/1.55  tff(c_494, plain, (![C_164]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_164))!='#skF_8' | ~r2_hidden(C_164, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_477, c_52])).
% 3.07/1.55  tff(c_498, plain, (![C_51]: (C_51!='#skF_8' | ~r2_hidden(C_51, k2_relat_1('#skF_9')) | ~r2_hidden(C_51, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_494])).
% 3.07/1.55  tff(c_501, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_60, c_498])).
% 3.07/1.55  tff(c_159, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_54])).
% 3.07/1.55  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_159])).
% 3.07/1.55  tff(c_504, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_434])).
% 3.07/1.55  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.55  tff(c_69, plain, (![B_77, A_78]: (~r1_tarski(B_77, A_78) | ~r2_hidden(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.07/1.55  tff(c_88, plain, (![A_80]: (~r1_tarski(A_80, '#skF_1'(A_80)) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_4, c_69])).
% 3.07/1.55  tff(c_93, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_88])).
% 3.07/1.55  tff(c_513, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_93])).
% 3.07/1.55  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_513])).
% 3.07/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.55  
% 3.07/1.55  Inference rules
% 3.07/1.55  ----------------------
% 3.07/1.55  #Ref     : 0
% 3.07/1.55  #Sup     : 91
% 3.07/1.55  #Fact    : 0
% 3.07/1.55  #Define  : 0
% 3.07/1.55  #Split   : 4
% 3.07/1.55  #Chain   : 0
% 3.07/1.55  #Close   : 0
% 3.07/1.55  
% 3.07/1.55  Ordering : KBO
% 3.07/1.55  
% 3.07/1.55  Simplification rules
% 3.07/1.55  ----------------------
% 3.07/1.55  #Subsume      : 14
% 3.07/1.55  #Demod        : 50
% 3.07/1.55  #Tautology    : 14
% 3.07/1.55  #SimpNegUnit  : 4
% 3.07/1.55  #BackRed      : 16
% 3.07/1.55  
% 3.07/1.55  #Partial instantiations: 0
% 3.07/1.55  #Strategies tried      : 1
% 3.07/1.55  
% 3.07/1.55  Timing (in seconds)
% 3.07/1.55  ----------------------
% 3.07/1.56  Preprocessing        : 0.32
% 3.07/1.56  Parsing              : 0.16
% 3.07/1.56  CNF conversion       : 0.03
% 3.07/1.56  Main loop            : 0.39
% 3.07/1.56  Inferencing          : 0.14
% 3.07/1.56  Reduction            : 0.11
% 3.07/1.56  Demodulation         : 0.08
% 3.07/1.56  BG Simplification    : 0.02
% 3.07/1.56  Subsumption          : 0.08
% 3.07/1.56  Abstraction          : 0.02
% 3.07/1.56  MUC search           : 0.00
% 3.07/1.56  Cooper               : 0.00
% 3.07/1.56  Total                : 0.75
% 3.07/1.56  Index Insertion      : 0.00
% 3.07/1.56  Index Deletion       : 0.00
% 3.07/1.56  Index Matching       : 0.00
% 3.07/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
