%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 217 expanded)
%              Number of leaves         :   42 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 420 expanded)
%              Number of equality atoms :   35 ( 115 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_30,plain,(
    ! [A_37,B_38] : v1_relat_1(k2_zfmisc_1(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_101,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_107,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_104])).

tff(c_32,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k9_relat_1(B_40,A_39),k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) != k1_xboole_0
      | k1_xboole_0 = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_107,c_38])).

tff(c_121,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_145,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_149,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_145])).

tff(c_150,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [B_31,A_30] :
      ( k1_tarski(B_31) = A_30
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,k1_tarski(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_180,plain,(
    ! [B_94,B_95] :
      ( k1_tarski(B_94) = k1_relat_1(B_95)
      | k1_relat_1(B_95) = k1_xboole_0
      | ~ v4_relat_1(B_95,k1_tarski(B_94))
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_150,c_18])).

tff(c_183,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_180])).

tff(c_186,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_183])).

tff(c_187,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_186])).

tff(c_279,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(k1_funct_1(B_103,A_104)) = k2_relat_1(B_103)
      | k1_tarski(A_104) != k1_relat_1(B_103)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_190,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_52])).

tff(c_46,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( k7_relset_1(A_48,B_49,C_50,D_51) = k9_relat_1(C_50,D_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_231,plain,(
    ! [D_51] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_51) = k9_relat_1('#skF_4',D_51) ),
    inference(resolution,[status(thm)],[c_190,c_46])).

tff(c_48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_189,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_48])).

tff(c_269,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_189])).

tff(c_285,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_269])).

tff(c_303,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_56,c_187,c_285])).

tff(c_307,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_303])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_307])).

tff(c_312,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_317,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_2])).

tff(c_34,plain,(
    ! [A_41] : k9_relat_1(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_316,plain,(
    ! [A_41] : k9_relat_1('#skF_4',A_41) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_312,c_34])).

tff(c_471,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k7_relset_1(A_139,B_140,C_141,D_142) = k9_relat_1(C_141,D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_473,plain,(
    ! [D_142] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_142) = k9_relat_1('#skF_4',D_142) ),
    inference(resolution,[status(thm)],[c_52,c_471])).

tff(c_475,plain,(
    ! [D_142] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_142) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_473])).

tff(c_476,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_48])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.33  
% 2.67/1.33  %Foreground sorts:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Background operators:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Foreground operators:
% 2.67/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.67/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.67/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.67/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.67/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.67/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.33  
% 2.67/1.34  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.67/1.34  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.67/1.34  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.67/1.34  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.67/1.34  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.67/1.34  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.67/1.34  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.67/1.34  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.67/1.34  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.67/1.34  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.67/1.34  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.34  tff(f_68, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.67/1.34  tff(c_30, plain, (![A_37, B_38]: (v1_relat_1(k2_zfmisc_1(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.34  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.67/1.34  tff(c_101, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.34  tff(c_104, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_101])).
% 2.67/1.34  tff(c_107, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_104])).
% 2.67/1.34  tff(c_32, plain, (![B_40, A_39]: (r1_tarski(k9_relat_1(B_40, A_39), k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.34  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.67/1.34  tff(c_38, plain, (![A_42]: (k1_relat_1(A_42)!=k1_xboole_0 | k1_xboole_0=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.67/1.34  tff(c_114, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_107, c_38])).
% 2.67/1.34  tff(c_121, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_114])).
% 2.67/1.34  tff(c_145, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.67/1.34  tff(c_149, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_145])).
% 2.67/1.34  tff(c_150, plain, (![B_79, A_80]: (r1_tarski(k1_relat_1(B_79), A_80) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.34  tff(c_18, plain, (![B_31, A_30]: (k1_tarski(B_31)=A_30 | k1_xboole_0=A_30 | ~r1_tarski(A_30, k1_tarski(B_31)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.34  tff(c_180, plain, (![B_94, B_95]: (k1_tarski(B_94)=k1_relat_1(B_95) | k1_relat_1(B_95)=k1_xboole_0 | ~v4_relat_1(B_95, k1_tarski(B_94)) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_150, c_18])).
% 2.67/1.34  tff(c_183, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_149, c_180])).
% 2.67/1.34  tff(c_186, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_183])).
% 2.67/1.34  tff(c_187, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_121, c_186])).
% 2.67/1.34  tff(c_279, plain, (![B_103, A_104]: (k1_tarski(k1_funct_1(B_103, A_104))=k2_relat_1(B_103) | k1_tarski(A_104)!=k1_relat_1(B_103) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.67/1.34  tff(c_190, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_52])).
% 2.67/1.34  tff(c_46, plain, (![A_48, B_49, C_50, D_51]: (k7_relset_1(A_48, B_49, C_50, D_51)=k9_relat_1(C_50, D_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.67/1.34  tff(c_231, plain, (![D_51]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_51)=k9_relat_1('#skF_4', D_51))), inference(resolution, [status(thm)], [c_190, c_46])).
% 2.67/1.34  tff(c_48, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.67/1.34  tff(c_189, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_48])).
% 2.67/1.34  tff(c_269, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_189])).
% 2.67/1.34  tff(c_285, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_279, c_269])).
% 2.67/1.34  tff(c_303, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_56, c_187, c_285])).
% 2.67/1.34  tff(c_307, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_303])).
% 2.67/1.34  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_307])).
% 2.67/1.34  tff(c_312, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_114])).
% 2.67/1.34  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.34  tff(c_317, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_2])).
% 2.67/1.34  tff(c_34, plain, (![A_41]: (k9_relat_1(k1_xboole_0, A_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.34  tff(c_316, plain, (![A_41]: (k9_relat_1('#skF_4', A_41)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_312, c_34])).
% 2.67/1.34  tff(c_471, plain, (![A_139, B_140, C_141, D_142]: (k7_relset_1(A_139, B_140, C_141, D_142)=k9_relat_1(C_141, D_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.67/1.34  tff(c_473, plain, (![D_142]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_142)=k9_relat_1('#skF_4', D_142))), inference(resolution, [status(thm)], [c_52, c_471])).
% 2.67/1.34  tff(c_475, plain, (![D_142]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_142)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_473])).
% 2.67/1.34  tff(c_476, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_48])).
% 2.67/1.34  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_476])).
% 2.67/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  Inference rules
% 2.67/1.34  ----------------------
% 2.67/1.34  #Ref     : 0
% 2.67/1.34  #Sup     : 83
% 2.67/1.34  #Fact    : 0
% 2.67/1.34  #Define  : 0
% 2.67/1.34  #Split   : 3
% 2.67/1.34  #Chain   : 0
% 2.67/1.34  #Close   : 0
% 2.67/1.34  
% 2.67/1.34  Ordering : KBO
% 2.67/1.34  
% 2.67/1.34  Simplification rules
% 2.67/1.34  ----------------------
% 2.67/1.34  #Subsume      : 3
% 2.67/1.34  #Demod        : 59
% 2.67/1.34  #Tautology    : 55
% 2.67/1.34  #SimpNegUnit  : 4
% 2.67/1.34  #BackRed      : 10
% 2.67/1.34  
% 2.67/1.34  #Partial instantiations: 0
% 2.67/1.34  #Strategies tried      : 1
% 2.67/1.34  
% 2.67/1.35  Timing (in seconds)
% 2.67/1.35  ----------------------
% 2.67/1.35  Preprocessing        : 0.34
% 2.67/1.35  Parsing              : 0.19
% 2.67/1.35  CNF conversion       : 0.02
% 2.67/1.35  Main loop            : 0.24
% 2.67/1.35  Inferencing          : 0.09
% 2.67/1.35  Reduction            : 0.08
% 2.67/1.35  Demodulation         : 0.06
% 2.67/1.35  BG Simplification    : 0.02
% 2.67/1.35  Subsumption          : 0.03
% 2.67/1.35  Abstraction          : 0.01
% 2.67/1.35  MUC search           : 0.00
% 2.67/1.35  Cooper               : 0.00
% 2.67/1.35  Total                : 0.62
% 2.67/1.35  Index Insertion      : 0.00
% 2.67/1.35  Index Deletion       : 0.00
% 2.67/1.35  Index Matching       : 0.00
% 2.67/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
