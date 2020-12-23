%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:38 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 148 expanded)
%              Number of leaves         :   41 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 300 expanded)
%              Number of equality atoms :   38 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_85,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_85])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_153,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_157,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_153])).

tff(c_183,plain,(
    ! [B_89,A_90,C_91] :
      ( k1_xboole_0 = B_89
      | k1_relset_1(A_90,B_89,C_91) = A_90
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_183])).

tff(c_189,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_157,c_186])).

tff(c_190,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_189])).

tff(c_110,plain,(
    ! [C_54,A_55,B_56] :
      ( v4_relat_1(C_54,A_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_114,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_110])).

tff(c_193,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_114])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [B_40,C_41,A_42] :
      ( r2_hidden(B_40,C_41)
      | ~ r1_tarski(k2_tarski(A_42,B_40),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_1,C_41] :
      ( r2_hidden(A_1,C_41)
      | ~ r1_tarski(k1_tarski(A_1),C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_256,plain,(
    ! [C_92] :
      ( r2_hidden('#skF_1',C_92)
      | ~ r1_tarski(k1_relat_1('#skF_3'),C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_79])).

tff(c_260,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1',A_16)
      | ~ v4_relat_1('#skF_3',A_16)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_256])).

tff(c_265,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_1',A_93)
      | ~ v4_relat_1('#skF_3',A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_260])).

tff(c_269,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_193,c_265])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(k1_funct_1(B_22,A_21)) = k11_relat_1(B_22,A_21)
      | ~ r2_hidden(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_272,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k11_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_269,c_26])).

tff(c_275,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k11_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_56,c_272])).

tff(c_162,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_166,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_162])).

tff(c_48,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_167,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_48])).

tff(c_276,plain,(
    k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_167])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_290,plain,(
    ! [A_94] :
      ( k9_relat_1(A_94,k1_relat_1('#skF_3')) = k11_relat_1(A_94,'#skF_1')
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_16])).

tff(c_24,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_297,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_24])).

tff(c_307,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_297])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  
% 2.39/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.45  
% 2.39/1.45  %Foreground sorts:
% 2.39/1.45  
% 2.39/1.45  
% 2.39/1.45  %Background operators:
% 2.39/1.45  
% 2.39/1.45  
% 2.39/1.45  %Foreground operators:
% 2.39/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.39/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.45  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.39/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.39/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.39/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.39/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.39/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.39/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.45  
% 2.72/1.46  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.72/1.46  tff(f_113, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.72/1.46  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.72/1.46  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.72/1.46  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.72/1.46  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.72/1.46  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.72/1.46  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.46  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.72/1.46  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.72/1.46  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.72/1.46  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.72/1.46  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.72/1.46  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.46  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.72/1.46  tff(c_85, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.46  tff(c_88, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_85])).
% 2.72/1.46  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_88])).
% 2.72/1.46  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.72/1.46  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.72/1.46  tff(c_54, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.72/1.46  tff(c_153, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.46  tff(c_157, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_153])).
% 2.72/1.46  tff(c_183, plain, (![B_89, A_90, C_91]: (k1_xboole_0=B_89 | k1_relset_1(A_90, B_89, C_91)=A_90 | ~v1_funct_2(C_91, A_90, B_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.46  tff(c_186, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_52, c_183])).
% 2.72/1.46  tff(c_189, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_157, c_186])).
% 2.72/1.46  tff(c_190, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_189])).
% 2.72/1.46  tff(c_110, plain, (![C_54, A_55, B_56]: (v4_relat_1(C_54, A_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.72/1.46  tff(c_114, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_110])).
% 2.72/1.46  tff(c_193, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_114])).
% 2.72/1.46  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.46  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.46  tff(c_76, plain, (![B_40, C_41, A_42]: (r2_hidden(B_40, C_41) | ~r1_tarski(k2_tarski(A_42, B_40), C_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.46  tff(c_79, plain, (![A_1, C_41]: (r2_hidden(A_1, C_41) | ~r1_tarski(k1_tarski(A_1), C_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_76])).
% 2.72/1.46  tff(c_256, plain, (![C_92]: (r2_hidden('#skF_1', C_92) | ~r1_tarski(k1_relat_1('#skF_3'), C_92))), inference(superposition, [status(thm), theory('equality')], [c_190, c_79])).
% 2.72/1.46  tff(c_260, plain, (![A_16]: (r2_hidden('#skF_1', A_16) | ~v4_relat_1('#skF_3', A_16) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_256])).
% 2.72/1.46  tff(c_265, plain, (![A_93]: (r2_hidden('#skF_1', A_93) | ~v4_relat_1('#skF_3', A_93))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_260])).
% 2.72/1.46  tff(c_269, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_193, c_265])).
% 2.72/1.46  tff(c_26, plain, (![B_22, A_21]: (k1_tarski(k1_funct_1(B_22, A_21))=k11_relat_1(B_22, A_21) | ~r2_hidden(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.72/1.46  tff(c_272, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k11_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_269, c_26])).
% 2.72/1.46  tff(c_275, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k11_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_56, c_272])).
% 2.72/1.46  tff(c_162, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.72/1.46  tff(c_166, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_162])).
% 2.72/1.46  tff(c_48, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.72/1.46  tff(c_167, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_48])).
% 2.72/1.46  tff(c_276, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_167])).
% 2.72/1.46  tff(c_16, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.46  tff(c_290, plain, (![A_94]: (k9_relat_1(A_94, k1_relat_1('#skF_3'))=k11_relat_1(A_94, '#skF_1') | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_190, c_16])).
% 2.72/1.46  tff(c_24, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.46  tff(c_297, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_290, c_24])).
% 2.72/1.46  tff(c_307, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_297])).
% 2.72/1.46  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_307])).
% 2.72/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.46  
% 2.72/1.46  Inference rules
% 2.72/1.46  ----------------------
% 2.72/1.46  #Ref     : 0
% 2.72/1.46  #Sup     : 56
% 2.72/1.46  #Fact    : 0
% 2.72/1.46  #Define  : 0
% 2.72/1.46  #Split   : 0
% 2.72/1.46  #Chain   : 0
% 2.72/1.46  #Close   : 0
% 2.72/1.46  
% 2.72/1.46  Ordering : KBO
% 2.72/1.46  
% 2.72/1.46  Simplification rules
% 2.72/1.46  ----------------------
% 2.72/1.46  #Subsume      : 1
% 2.72/1.46  #Demod        : 26
% 2.72/1.46  #Tautology    : 35
% 2.72/1.46  #SimpNegUnit  : 5
% 2.72/1.46  #BackRed      : 7
% 2.72/1.46  
% 2.72/1.46  #Partial instantiations: 0
% 2.72/1.46  #Strategies tried      : 1
% 2.72/1.46  
% 2.72/1.46  Timing (in seconds)
% 2.72/1.46  ----------------------
% 2.72/1.47  Preprocessing        : 0.46
% 2.72/1.47  Parsing              : 0.20
% 2.72/1.47  CNF conversion       : 0.04
% 2.72/1.47  Main loop            : 0.23
% 2.72/1.47  Inferencing          : 0.09
% 2.72/1.47  Reduction            : 0.08
% 2.72/1.47  Demodulation         : 0.05
% 2.72/1.47  BG Simplification    : 0.03
% 2.72/1.47  Subsumption          : 0.04
% 2.72/1.47  Abstraction          : 0.01
% 2.72/1.47  MUC search           : 0.00
% 2.72/1.47  Cooper               : 0.00
% 2.72/1.47  Total                : 0.73
% 2.72/1.47  Index Insertion      : 0.00
% 2.72/1.47  Index Deletion       : 0.00
% 2.72/1.47  Index Matching       : 0.00
% 2.72/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
