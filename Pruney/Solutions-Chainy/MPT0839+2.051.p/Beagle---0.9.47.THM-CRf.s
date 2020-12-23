%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 145 expanded)
%              Number of leaves         :   39 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 260 expanded)
%              Number of equality atoms :   27 (  69 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_50,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [A_31,B_32] : v1_relat_1(k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_89,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_99,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_95])).

tff(c_140,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_149,plain,(
    v4_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_140])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) = k1_xboole_0
      | k1_relat_1(A_33) != k1_xboole_0
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_36])).

tff(c_108,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_443,plain,(
    ! [A_150,B_151] :
      ( r2_hidden(k4_tarski('#skF_1'(A_150,B_151),'#skF_2'(A_150,B_151)),A_150)
      | r2_hidden('#skF_3'(A_150,B_151),B_151)
      | k1_relat_1(A_150) = B_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_298,plain,(
    ! [C_117,A_118] :
      ( r2_hidden(k4_tarski(C_117,'#skF_4'(A_118,k1_relat_1(A_118),C_117)),A_118)
      | ~ r2_hidden(C_117,k1_relat_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_313,plain,(
    ! [C_117] :
      ( r2_hidden(k4_tarski(C_117,'#skF_4'(k1_xboole_0,k1_xboole_0,C_117)),k1_xboole_0)
      | ~ r2_hidden(C_117,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_298])).

tff(c_350,plain,(
    ! [C_126] :
      ( r2_hidden(k4_tarski(C_126,'#skF_4'(k1_xboole_0,k1_xboole_0,C_126)),k1_xboole_0)
      | ~ r2_hidden(C_126,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_313])).

tff(c_38,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_358,plain,(
    ! [C_126] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_126,'#skF_4'(k1_xboole_0,k1_xboole_0,C_126)))
      | ~ r2_hidden(C_126,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_350,c_38])).

tff(c_366,plain,(
    ! [C_126] : ~ r2_hidden(C_126,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_358])).

tff(c_447,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_151),B_151)
      | k1_relat_1(k1_xboole_0) = B_151 ) ),
    inference(resolution,[status(thm)],[c_443,c_366])).

tff(c_466,plain,(
    ! [B_152] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_152),B_152)
      | k1_xboole_0 = B_152 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_447])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_220,plain,(
    ! [A_94,B_3,A_2] :
      ( m1_subset_1(A_94,B_3)
      | ~ r2_hidden(A_94,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_500,plain,(
    ! [B_155,B_156] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_155),B_156)
      | ~ r1_tarski(B_155,B_156)
      | k1_xboole_0 = B_155 ) ),
    inference(resolution,[status(thm)],[c_466,c_220])).

tff(c_265,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_274,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_265])).

tff(c_48,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k1_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ m1_subset_1(D_56,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_275,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_56,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_48])).

tff(c_474,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_466,c_275])).

tff(c_484,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_474])).

tff(c_503,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_500,c_484])).

tff(c_533,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_503])).

tff(c_543,plain,
    ( ~ v4_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_533])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_149,c_543])).

tff(c_548,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_694,plain,(
    ! [A_190,B_191,C_192] :
      ( k2_relset_1(A_190,B_191,C_192) = k2_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_701,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_694])).

tff(c_704,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_701])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  
% 2.98/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.98/1.49  
% 2.98/1.49  %Foreground sorts:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Background operators:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Foreground operators:
% 2.98/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.98/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.98/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.98/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.98/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.98/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.98/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.98/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.49  
% 3.15/1.51  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.15/1.51  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.15/1.51  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.15/1.51  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.15/1.51  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.15/1.51  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.15/1.51  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.15/1.51  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.15/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.51  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.15/1.51  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.15/1.51  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.15/1.51  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.51  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.15/1.51  tff(c_50, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.15/1.51  tff(c_28, plain, (![A_31, B_32]: (v1_relat_1(k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.51  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.15/1.51  tff(c_89, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.51  tff(c_95, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_89])).
% 3.15/1.51  tff(c_99, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_95])).
% 3.15/1.51  tff(c_140, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.15/1.51  tff(c_149, plain, (v4_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_140])).
% 3.15/1.51  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.51  tff(c_36, plain, (![A_33]: (k2_relat_1(A_33)=k1_xboole_0 | k1_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.51  tff(c_106, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_36])).
% 3.15/1.51  tff(c_108, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 3.15/1.51  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.51  tff(c_443, plain, (![A_150, B_151]: (r2_hidden(k4_tarski('#skF_1'(A_150, B_151), '#skF_2'(A_150, B_151)), A_150) | r2_hidden('#skF_3'(A_150, B_151), B_151) | k1_relat_1(A_150)=B_151)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.51  tff(c_298, plain, (![C_117, A_118]: (r2_hidden(k4_tarski(C_117, '#skF_4'(A_118, k1_relat_1(A_118), C_117)), A_118) | ~r2_hidden(C_117, k1_relat_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.51  tff(c_313, plain, (![C_117]: (r2_hidden(k4_tarski(C_117, '#skF_4'(k1_xboole_0, k1_xboole_0, C_117)), k1_xboole_0) | ~r2_hidden(C_117, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_298])).
% 3.15/1.51  tff(c_350, plain, (![C_126]: (r2_hidden(k4_tarski(C_126, '#skF_4'(k1_xboole_0, k1_xboole_0, C_126)), k1_xboole_0) | ~r2_hidden(C_126, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_313])).
% 3.15/1.51  tff(c_38, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.51  tff(c_358, plain, (![C_126]: (~r1_tarski(k1_xboole_0, k4_tarski(C_126, '#skF_4'(k1_xboole_0, k1_xboole_0, C_126))) | ~r2_hidden(C_126, k1_xboole_0))), inference(resolution, [status(thm)], [c_350, c_38])).
% 3.15/1.51  tff(c_366, plain, (![C_126]: (~r2_hidden(C_126, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_358])).
% 3.15/1.51  tff(c_447, plain, (![B_151]: (r2_hidden('#skF_3'(k1_xboole_0, B_151), B_151) | k1_relat_1(k1_xboole_0)=B_151)), inference(resolution, [status(thm)], [c_443, c_366])).
% 3.15/1.51  tff(c_466, plain, (![B_152]: (r2_hidden('#skF_3'(k1_xboole_0, B_152), B_152) | k1_xboole_0=B_152)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_447])).
% 3.15/1.51  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.51  tff(c_215, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.51  tff(c_220, plain, (![A_94, B_3, A_2]: (m1_subset_1(A_94, B_3) | ~r2_hidden(A_94, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_6, c_215])).
% 3.15/1.51  tff(c_500, plain, (![B_155, B_156]: (m1_subset_1('#skF_3'(k1_xboole_0, B_155), B_156) | ~r1_tarski(B_155, B_156) | k1_xboole_0=B_155)), inference(resolution, [status(thm)], [c_466, c_220])).
% 3.15/1.51  tff(c_265, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.15/1.51  tff(c_274, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_265])).
% 3.15/1.51  tff(c_48, plain, (![D_56]: (~r2_hidden(D_56, k1_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_subset_1(D_56, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.15/1.51  tff(c_275, plain, (![D_56]: (~r2_hidden(D_56, k1_relat_1('#skF_7')) | ~m1_subset_1(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_48])).
% 3.15/1.51  tff(c_474, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_466, c_275])).
% 3.15/1.51  tff(c_484, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_108, c_474])).
% 3.15/1.51  tff(c_503, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_500, c_484])).
% 3.15/1.51  tff(c_533, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_108, c_503])).
% 3.15/1.51  tff(c_543, plain, (~v4_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_14, c_533])).
% 3.15/1.51  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_149, c_543])).
% 3.15/1.51  tff(c_548, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 3.15/1.51  tff(c_694, plain, (![A_190, B_191, C_192]: (k2_relset_1(A_190, B_191, C_192)=k2_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.51  tff(c_701, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_694])).
% 3.15/1.51  tff(c_704, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_548, c_701])).
% 3.15/1.51  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_704])).
% 3.15/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  Inference rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Ref     : 0
% 3.15/1.51  #Sup     : 125
% 3.15/1.51  #Fact    : 0
% 3.15/1.51  #Define  : 0
% 3.15/1.51  #Split   : 4
% 3.15/1.51  #Chain   : 0
% 3.15/1.51  #Close   : 0
% 3.15/1.51  
% 3.15/1.51  Ordering : KBO
% 3.15/1.51  
% 3.15/1.51  Simplification rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Subsume      : 16
% 3.15/1.51  #Demod        : 72
% 3.15/1.51  #Tautology    : 52
% 3.15/1.51  #SimpNegUnit  : 13
% 3.15/1.51  #BackRed      : 6
% 3.15/1.51  
% 3.15/1.51  #Partial instantiations: 0
% 3.15/1.51  #Strategies tried      : 1
% 3.15/1.51  
% 3.15/1.51  Timing (in seconds)
% 3.15/1.51  ----------------------
% 3.15/1.51  Preprocessing        : 0.36
% 3.15/1.51  Parsing              : 0.18
% 3.15/1.51  CNF conversion       : 0.03
% 3.15/1.51  Main loop            : 0.33
% 3.15/1.51  Inferencing          : 0.12
% 3.15/1.51  Reduction            : 0.10
% 3.15/1.51  Demodulation         : 0.07
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.51  Subsumption          : 0.05
% 3.15/1.51  Abstraction          : 0.02
% 3.15/1.51  MUC search           : 0.00
% 3.15/1.51  Cooper               : 0.00
% 3.15/1.51  Total                : 0.72
% 3.15/1.51  Index Insertion      : 0.00
% 3.15/1.51  Index Deletion       : 0.00
% 3.15/1.51  Index Matching       : 0.00
% 3.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
