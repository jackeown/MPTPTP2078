%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:07 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 290 expanded)
%              Number of leaves         :   38 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 629 expanded)
%              Number of equality atoms :   14 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_96,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_288,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_292,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_288])).

tff(c_54,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_294,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_74])).

tff(c_18,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_85,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_30,plain,(
    ! [B_36,A_35] :
      ( k7_relat_1(B_36,A_35) = B_36
      | ~ v4_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,
    ( k7_relat_1('#skF_8','#skF_7') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_89,c_30])).

tff(c_95,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_92])).

tff(c_28,plain,(
    ! [B_34,A_33] :
      ( k2_relat_1(k7_relat_1(B_34,A_33)) = k9_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,
    ( k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_28])).

tff(c_103,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_99])).

tff(c_521,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_hidden('#skF_5'(A_178,B_179,C_180),B_179)
      | ~ r2_hidden(A_178,k9_relat_1(C_180,B_179))
      | ~ v1_relat_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_551,plain,(
    ! [A_185,B_186,C_187] :
      ( m1_subset_1('#skF_5'(A_185,B_186,C_187),B_186)
      | ~ r2_hidden(A_185,k9_relat_1(C_187,B_186))
      | ~ v1_relat_1(C_187) ) ),
    inference(resolution,[status(thm)],[c_521,c_2])).

tff(c_562,plain,(
    ! [A_185] :
      ( m1_subset_1('#skF_5'(A_185,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_185,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_551])).

tff(c_568,plain,(
    ! [A_188] :
      ( m1_subset_1('#skF_5'(A_188,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_188,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_562])).

tff(c_591,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_294,c_568])).

tff(c_599,plain,(
    ! [A_197,B_198,C_199] :
      ( r2_hidden(k4_tarski('#skF_5'(A_197,B_198,C_199),A_197),C_199)
      | ~ r2_hidden(A_197,k9_relat_1(C_199,B_198))
      | ~ v1_relat_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [E_84] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_469,plain,(
    ! [E_84] :
      ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
      | ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_44])).

tff(c_470,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_306,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_5'(A_142,B_143,C_144),B_143)
      | ~ r2_hidden(A_142,k9_relat_1(C_144,B_143))
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_336,plain,(
    ! [A_149,B_150,C_151] :
      ( m1_subset_1('#skF_5'(A_149,B_150,C_151),B_150)
      | ~ r2_hidden(A_149,k9_relat_1(C_151,B_150))
      | ~ v1_relat_1(C_151) ) ),
    inference(resolution,[status(thm)],[c_306,c_2])).

tff(c_347,plain,(
    ! [A_149] :
      ( m1_subset_1('#skF_5'(A_149,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_149,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_336])).

tff(c_353,plain,(
    ! [A_152] :
      ( m1_subset_1('#skF_5'(A_152,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_152,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_347])).

tff(c_372,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_294,c_353])).

tff(c_405,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden(k4_tarski('#skF_5'(A_166,B_167,C_168),A_166),C_168)
      | ~ r2_hidden(A_166,k9_relat_1(C_168,B_167))
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    ! [E_84] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_299,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_416,plain,(
    ! [B_167] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_167,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_167))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_405,c_299])).

tff(c_456,plain,(
    ! [B_172] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_172,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_172)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_416])).

tff(c_459,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_456])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_372,c_459])).

tff(c_463,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k2_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(D_24,C_21),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_473,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_463,c_8])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_473])).

tff(c_481,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_610,plain,(
    ! [B_198] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_198,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_198))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_599,c_481])).

tff(c_650,plain,(
    ! [B_203] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_203,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_203)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_610])).

tff(c_653,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_650])).

tff(c_656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_591,c_653])).

tff(c_658,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_670,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_52])).

tff(c_677,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_670,c_8])).

tff(c_704,plain,(
    ! [A_212,B_213,C_214] :
      ( k2_relset_1(A_212,B_213,C_214) = k2_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_708,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_704])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_703,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_50])).

tff(c_710,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_703])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.84/1.43  
% 2.84/1.43  %Foreground sorts:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Background operators:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Foreground operators:
% 2.84/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.43  tff('#skF_11', type, '#skF_11': $i).
% 2.84/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.84/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.84/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.84/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.84/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.43  
% 2.84/1.45  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 2.84/1.45  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.84/1.45  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.84/1.45  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.84/1.45  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.45  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.84/1.45  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.84/1.45  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.84/1.45  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.84/1.45  tff(f_44, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.84/1.45  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_288, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_292, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_288])).
% 2.84/1.45  tff(c_54, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_74, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.84/1.45  tff(c_294, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_74])).
% 2.84/1.45  tff(c_18, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.45  tff(c_57, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.84/1.45  tff(c_60, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_57])).
% 2.84/1.45  tff(c_63, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 2.84/1.45  tff(c_85, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.45  tff(c_89, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_85])).
% 2.84/1.45  tff(c_30, plain, (![B_36, A_35]: (k7_relat_1(B_36, A_35)=B_36 | ~v4_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.45  tff(c_92, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_89, c_30])).
% 2.84/1.45  tff(c_95, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_92])).
% 2.84/1.45  tff(c_28, plain, (![B_34, A_33]: (k2_relat_1(k7_relat_1(B_34, A_33))=k9_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.45  tff(c_99, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_95, c_28])).
% 2.84/1.45  tff(c_103, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_99])).
% 2.84/1.45  tff(c_521, plain, (![A_178, B_179, C_180]: (r2_hidden('#skF_5'(A_178, B_179, C_180), B_179) | ~r2_hidden(A_178, k9_relat_1(C_180, B_179)) | ~v1_relat_1(C_180))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.45  tff(c_551, plain, (![A_185, B_186, C_187]: (m1_subset_1('#skF_5'(A_185, B_186, C_187), B_186) | ~r2_hidden(A_185, k9_relat_1(C_187, B_186)) | ~v1_relat_1(C_187))), inference(resolution, [status(thm)], [c_521, c_2])).
% 2.84/1.45  tff(c_562, plain, (![A_185]: (m1_subset_1('#skF_5'(A_185, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_185, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_551])).
% 2.84/1.45  tff(c_568, plain, (![A_188]: (m1_subset_1('#skF_5'(A_188, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_188, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_562])).
% 2.84/1.45  tff(c_591, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_294, c_568])).
% 2.84/1.45  tff(c_599, plain, (![A_197, B_198, C_199]: (r2_hidden(k4_tarski('#skF_5'(A_197, B_198, C_199), A_197), C_199) | ~r2_hidden(A_197, k9_relat_1(C_199, B_198)) | ~v1_relat_1(C_199))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_44, plain, (![E_84]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_469, plain, (![E_84]: (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | ~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_44])).
% 2.84/1.45  tff(c_470, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_469])).
% 2.84/1.45  tff(c_306, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_5'(A_142, B_143, C_144), B_143) | ~r2_hidden(A_142, k9_relat_1(C_144, B_143)) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_336, plain, (![A_149, B_150, C_151]: (m1_subset_1('#skF_5'(A_149, B_150, C_151), B_150) | ~r2_hidden(A_149, k9_relat_1(C_151, B_150)) | ~v1_relat_1(C_151))), inference(resolution, [status(thm)], [c_306, c_2])).
% 2.84/1.45  tff(c_347, plain, (![A_149]: (m1_subset_1('#skF_5'(A_149, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_149, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_336])).
% 2.84/1.45  tff(c_353, plain, (![A_152]: (m1_subset_1('#skF_5'(A_152, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_152, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_347])).
% 2.84/1.45  tff(c_372, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_294, c_353])).
% 2.84/1.45  tff(c_405, plain, (![A_166, B_167, C_168]: (r2_hidden(k4_tarski('#skF_5'(A_166, B_167, C_168), A_166), C_168) | ~r2_hidden(A_166, k9_relat_1(C_168, B_167)) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_46, plain, (![E_84]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_299, plain, (![E_84]: (~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 2.84/1.45  tff(c_416, plain, (![B_167]: (~m1_subset_1('#skF_5'('#skF_11', B_167, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_167)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_405, c_299])).
% 2.84/1.45  tff(c_456, plain, (![B_172]: (~m1_subset_1('#skF_5'('#skF_11', B_172, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_172)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_416])).
% 2.84/1.45  tff(c_459, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_456])).
% 2.84/1.45  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_294, c_372, c_459])).
% 2.84/1.45  tff(c_463, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 2.84/1.45  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k2_relat_1(A_6)) | ~r2_hidden(k4_tarski(D_24, C_21), A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.45  tff(c_473, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_463, c_8])).
% 2.84/1.45  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_473])).
% 2.84/1.45  tff(c_481, plain, (![E_84]: (~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(splitRight, [status(thm)], [c_469])).
% 2.84/1.45  tff(c_610, plain, (![B_198]: (~m1_subset_1('#skF_5'('#skF_11', B_198, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_198)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_599, c_481])).
% 2.84/1.45  tff(c_650, plain, (![B_203]: (~m1_subset_1('#skF_5'('#skF_11', B_203, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_203)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_610])).
% 2.84/1.45  tff(c_653, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_650])).
% 2.84/1.45  tff(c_656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_294, c_591, c_653])).
% 2.84/1.45  tff(c_658, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_54])).
% 2.84/1.45  tff(c_52, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_670, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_658, c_52])).
% 2.84/1.45  tff(c_677, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_670, c_8])).
% 2.84/1.45  tff(c_704, plain, (![A_212, B_213, C_214]: (k2_relset_1(A_212, B_213, C_214)=k2_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_708, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_704])).
% 2.84/1.45  tff(c_50, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_703, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_658, c_50])).
% 2.84/1.45  tff(c_710, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_703])).
% 2.84/1.45  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_677, c_710])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 132
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 4
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 3
% 2.84/1.45  #Demod        : 42
% 2.84/1.45  #Tautology    : 29
% 2.84/1.45  #SimpNegUnit  : 3
% 2.84/1.45  #BackRed      : 6
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.33
% 2.84/1.45  Parsing              : 0.17
% 2.84/1.45  CNF conversion       : 0.03
% 2.84/1.45  Main loop            : 0.34
% 2.84/1.45  Inferencing          : 0.13
% 2.84/1.45  Reduction            : 0.10
% 2.84/1.45  Demodulation         : 0.07
% 2.84/1.45  BG Simplification    : 0.02
% 2.84/1.45  Subsumption          : 0.06
% 2.84/1.45  Abstraction          : 0.02
% 2.84/1.45  MUC search           : 0.00
% 2.84/1.45  Cooper               : 0.00
% 2.84/1.45  Total                : 0.71
% 2.84/1.45  Index Insertion      : 0.00
% 2.84/1.45  Index Deletion       : 0.00
% 2.84/1.45  Index Matching       : 0.00
% 2.84/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
