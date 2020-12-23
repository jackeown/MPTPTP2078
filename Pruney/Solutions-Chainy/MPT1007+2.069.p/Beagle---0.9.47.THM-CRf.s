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
% DateTime   : Thu Dec  3 10:14:20 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   76 (  94 expanded)
%              Number of leaves         :   41 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 165 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_50,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_114,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_114])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_202,plain,(
    ! [C_92,B_93,A_94] :
      ( v5_relat_1(C_92,B_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_211,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_202])).

tff(c_48,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v5_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_78,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_281,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_290,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_281])).

tff(c_519,plain,(
    ! [B_226,A_227,C_228] :
      ( k1_xboole_0 = B_226
      | k1_relset_1(A_227,B_226,C_228) = A_227
      | ~ v1_funct_2(C_228,A_227,B_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_526,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_519])).

tff(c_530,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_290,c_526])).

tff(c_531,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_530])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    ! [A_76,B_77,C_78] : k2_enumset1(A_76,A_76,B_77,C_78) = k1_enumset1(A_76,B_77,C_78) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [F_14,A_7,B_8,C_9] : r2_hidden(F_14,k2_enumset1(A_7,B_8,C_9,F_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_179,plain,(
    ! [C_79,A_80,B_81] : r2_hidden(C_79,k1_enumset1(A_80,B_81,C_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_10])).

tff(c_183,plain,(
    ! [B_82,A_83] : r2_hidden(B_82,k2_tarski(A_83,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_186,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_183])).

tff(c_546,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_186])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_344,plain,(
    ! [B_142,A_143] :
      ( r2_hidden(k1_funct_1(B_142,A_143),k2_relat_1(B_142))
      | ~ r2_hidden(A_143,k1_relat_1(B_142))
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_685,plain,(
    ! [B_263,A_264,A_265] :
      ( r2_hidden(k1_funct_1(B_263,A_264),A_265)
      | ~ m1_subset_1(k2_relat_1(B_263),k1_zfmisc_1(A_265))
      | ~ r2_hidden(A_264,k1_relat_1(B_263))
      | ~ v1_funct_1(B_263)
      | ~ v1_relat_1(B_263) ) ),
    inference(resolution,[status(thm)],[c_344,c_38])).

tff(c_690,plain,(
    ! [B_266,A_267,B_268] :
      ( r2_hidden(k1_funct_1(B_266,A_267),B_268)
      | ~ r2_hidden(A_267,k1_relat_1(B_266))
      | ~ v1_funct_1(B_266)
      | ~ v1_relat_1(B_266)
      | ~ r1_tarski(k2_relat_1(B_266),B_268) ) ),
    inference(resolution,[status(thm)],[c_42,c_685])).

tff(c_72,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_715,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_690,c_72])).

tff(c_724,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_80,c_546,c_715])).

tff(c_727,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_724])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_211,c_727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.50  
% 3.27/1.50  %Foreground sorts:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Background operators:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Foreground operators:
% 3.27/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.27/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.27/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.50  
% 3.42/1.52  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.42/1.52  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.42/1.52  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.42/1.52  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.52  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.42/1.52  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.52  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.42/1.52  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.42/1.52  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.42/1.52  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.42/1.52  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 3.42/1.52  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.42/1.52  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.42/1.52  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.42/1.52  tff(c_50, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.42/1.52  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.42/1.52  tff(c_114, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.52  tff(c_120, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_114])).
% 3.42/1.52  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_120])).
% 3.42/1.52  tff(c_202, plain, (![C_92, B_93, A_94]: (v5_relat_1(C_92, B_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.42/1.52  tff(c_211, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_202])).
% 3.42/1.52  tff(c_48, plain, (![B_25, A_24]: (r1_tarski(k2_relat_1(B_25), A_24) | ~v5_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.42/1.52  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.42/1.52  tff(c_74, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.42/1.52  tff(c_78, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.42/1.52  tff(c_281, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.42/1.52  tff(c_290, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_281])).
% 3.42/1.52  tff(c_519, plain, (![B_226, A_227, C_228]: (k1_xboole_0=B_226 | k1_relset_1(A_227, B_226, C_228)=A_227 | ~v1_funct_2(C_228, A_227, B_226) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.42/1.52  tff(c_526, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_76, c_519])).
% 3.42/1.52  tff(c_530, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_290, c_526])).
% 3.42/1.52  tff(c_531, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_530])).
% 3.42/1.52  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.52  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.52  tff(c_158, plain, (![A_76, B_77, C_78]: (k2_enumset1(A_76, A_76, B_77, C_78)=k1_enumset1(A_76, B_77, C_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.52  tff(c_10, plain, (![F_14, A_7, B_8, C_9]: (r2_hidden(F_14, k2_enumset1(A_7, B_8, C_9, F_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.42/1.52  tff(c_179, plain, (![C_79, A_80, B_81]: (r2_hidden(C_79, k1_enumset1(A_80, B_81, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_10])).
% 3.42/1.52  tff(c_183, plain, (![B_82, A_83]: (r2_hidden(B_82, k2_tarski(A_83, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_179])).
% 3.42/1.52  tff(c_186, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_183])).
% 3.42/1.52  tff(c_546, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_531, c_186])).
% 3.42/1.52  tff(c_42, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.42/1.52  tff(c_344, plain, (![B_142, A_143]: (r2_hidden(k1_funct_1(B_142, A_143), k2_relat_1(B_142)) | ~r2_hidden(A_143, k1_relat_1(B_142)) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.42/1.52  tff(c_38, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.42/1.52  tff(c_685, plain, (![B_263, A_264, A_265]: (r2_hidden(k1_funct_1(B_263, A_264), A_265) | ~m1_subset_1(k2_relat_1(B_263), k1_zfmisc_1(A_265)) | ~r2_hidden(A_264, k1_relat_1(B_263)) | ~v1_funct_1(B_263) | ~v1_relat_1(B_263))), inference(resolution, [status(thm)], [c_344, c_38])).
% 3.42/1.52  tff(c_690, plain, (![B_266, A_267, B_268]: (r2_hidden(k1_funct_1(B_266, A_267), B_268) | ~r2_hidden(A_267, k1_relat_1(B_266)) | ~v1_funct_1(B_266) | ~v1_relat_1(B_266) | ~r1_tarski(k2_relat_1(B_266), B_268))), inference(resolution, [status(thm)], [c_42, c_685])).
% 3.42/1.52  tff(c_72, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.42/1.52  tff(c_715, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_690, c_72])).
% 3.42/1.52  tff(c_724, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_80, c_546, c_715])).
% 3.42/1.52  tff(c_727, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_724])).
% 3.42/1.52  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_211, c_727])).
% 3.42/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.52  
% 3.42/1.52  Inference rules
% 3.42/1.52  ----------------------
% 3.42/1.52  #Ref     : 0
% 3.42/1.52  #Sup     : 135
% 3.42/1.52  #Fact    : 0
% 3.42/1.52  #Define  : 0
% 3.42/1.52  #Split   : 1
% 3.42/1.52  #Chain   : 0
% 3.42/1.52  #Close   : 0
% 3.42/1.52  
% 3.42/1.52  Ordering : KBO
% 3.42/1.52  
% 3.42/1.52  Simplification rules
% 3.42/1.52  ----------------------
% 3.42/1.52  #Subsume      : 20
% 3.42/1.52  #Demod        : 43
% 3.42/1.52  #Tautology    : 46
% 3.42/1.52  #SimpNegUnit  : 6
% 3.42/1.52  #BackRed      : 5
% 3.42/1.52  
% 3.42/1.52  #Partial instantiations: 0
% 3.42/1.52  #Strategies tried      : 1
% 3.42/1.52  
% 3.42/1.52  Timing (in seconds)
% 3.42/1.52  ----------------------
% 3.42/1.52  Preprocessing        : 0.35
% 3.42/1.52  Parsing              : 0.17
% 3.42/1.52  CNF conversion       : 0.03
% 3.42/1.52  Main loop            : 0.39
% 3.42/1.52  Inferencing          : 0.14
% 3.42/1.52  Reduction            : 0.12
% 3.42/1.52  Demodulation         : 0.08
% 3.42/1.52  BG Simplification    : 0.02
% 3.42/1.52  Subsumption          : 0.08
% 3.42/1.52  Abstraction          : 0.02
% 3.42/1.52  MUC search           : 0.00
% 3.42/1.52  Cooper               : 0.00
% 3.42/1.52  Total                : 0.78
% 3.42/1.52  Index Insertion      : 0.00
% 3.42/1.52  Index Deletion       : 0.00
% 3.42/1.52  Index Matching       : 0.00
% 3.42/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
