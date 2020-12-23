%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 244 expanded)
%              Number of leaves         :   42 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 466 expanded)
%              Number of equality atoms :   40 ( 141 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_102,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_102])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_38])).

tff(c_134,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_248,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_256,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_248])).

tff(c_287,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_290,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_256,c_287])).

tff(c_296,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_290])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_306,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_40])).

tff(c_315,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_306])).

tff(c_331,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_315,c_331])).

tff(c_353,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_334])).

tff(c_549,plain,(
    ! [B_101,A_102] :
      ( k1_tarski(k1_funct_1(B_101,A_102)) = k2_relat_1(B_101)
      | k1_tarski(A_102) != k1_relat_1(B_101)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_365,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_58])).

tff(c_464,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_470,plain,(
    ! [D_89] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_89) = k9_relat_1('#skF_4',D_89) ),
    inference(resolution,[status(thm)],[c_365,c_464])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_364,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_54])).

tff(c_490,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_364])).

tff(c_555,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_490])).

tff(c_564,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62,c_353,c_555])).

tff(c_568,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_564])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_568])).

tff(c_573,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_580,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_8])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_582,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_573,c_32])).

tff(c_598,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1('#skF_4',A_16),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_26])).

tff(c_634,plain,(
    ! [A_109] : r1_tarski(k9_relat_1('#skF_4',A_109),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_598])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_636,plain,(
    ! [A_109] :
      ( k9_relat_1('#skF_4',A_109) = '#skF_4'
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_109)) ) ),
    inference(resolution,[status(thm)],[c_634,c_2])).

tff(c_639,plain,(
    ! [A_109] : k9_relat_1('#skF_4',A_109) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_636])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_579,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_22])).

tff(c_856,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k7_relset_1(A_144,B_145,C_146,D_147) = k9_relat_1(C_146,D_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_859,plain,(
    ! [A_144,B_145,D_147] : k7_relset_1(A_144,B_145,'#skF_4',D_147) = k9_relat_1('#skF_4',D_147) ),
    inference(resolution,[status(thm)],[c_579,c_856])).

tff(c_861,plain,(
    ! [A_144,B_145,D_147] : k7_relset_1(A_144,B_145,'#skF_4',D_147) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_859])).

tff(c_862,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_54])).

tff(c_865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:48:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.39  
% 2.81/1.39  %Foreground sorts:
% 2.81/1.39  
% 2.81/1.39  
% 2.81/1.39  %Background operators:
% 2.81/1.39  
% 2.81/1.39  
% 2.81/1.39  %Foreground operators:
% 2.81/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.81/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.39  
% 2.81/1.41  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.81/1.41  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.81/1.41  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.81/1.41  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.81/1.41  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.41  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.81/1.41  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.81/1.41  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.81/1.41  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.81/1.41  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.81/1.41  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.41  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.81/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.41  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.81/1.41  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.81/1.41  tff(c_102, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.81/1.41  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_102])).
% 2.81/1.41  tff(c_26, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.41  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.81/1.41  tff(c_38, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.41  tff(c_119, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_110, c_38])).
% 2.81/1.41  tff(c_134, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_119])).
% 2.81/1.41  tff(c_248, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.81/1.41  tff(c_256, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_248])).
% 2.81/1.41  tff(c_287, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.41  tff(c_290, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_256, c_287])).
% 2.81/1.41  tff(c_296, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_290])).
% 2.81/1.41  tff(c_40, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.41  tff(c_306, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_296, c_40])).
% 2.81/1.41  tff(c_315, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_306])).
% 2.81/1.41  tff(c_331, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.41  tff(c_334, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_315, c_331])).
% 2.81/1.41  tff(c_353, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_134, c_334])).
% 2.81/1.41  tff(c_549, plain, (![B_101, A_102]: (k1_tarski(k1_funct_1(B_101, A_102))=k2_relat_1(B_101) | k1_tarski(A_102)!=k1_relat_1(B_101) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.81/1.41  tff(c_365, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_58])).
% 2.81/1.41  tff(c_464, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.81/1.41  tff(c_470, plain, (![D_89]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_89)=k9_relat_1('#skF_4', D_89))), inference(resolution, [status(thm)], [c_365, c_464])).
% 2.81/1.41  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.81/1.41  tff(c_364, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_54])).
% 2.81/1.41  tff(c_490, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_364])).
% 2.81/1.41  tff(c_555, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_549, c_490])).
% 2.81/1.41  tff(c_564, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_62, c_353, c_555])).
% 2.81/1.41  tff(c_568, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_564])).
% 2.81/1.41  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_568])).
% 2.81/1.41  tff(c_573, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_119])).
% 2.81/1.41  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.41  tff(c_580, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_8])).
% 2.81/1.41  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.41  tff(c_582, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_573, c_573, c_32])).
% 2.81/1.41  tff(c_598, plain, (![A_16]: (r1_tarski(k9_relat_1('#skF_4', A_16), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_26])).
% 2.81/1.41  tff(c_634, plain, (![A_109]: (r1_tarski(k9_relat_1('#skF_4', A_109), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_598])).
% 2.81/1.41  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.41  tff(c_636, plain, (![A_109]: (k9_relat_1('#skF_4', A_109)='#skF_4' | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_109)))), inference(resolution, [status(thm)], [c_634, c_2])).
% 2.81/1.41  tff(c_639, plain, (![A_109]: (k9_relat_1('#skF_4', A_109)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_636])).
% 2.81/1.41  tff(c_22, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.41  tff(c_579, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_22])).
% 2.81/1.41  tff(c_856, plain, (![A_144, B_145, C_146, D_147]: (k7_relset_1(A_144, B_145, C_146, D_147)=k9_relat_1(C_146, D_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.81/1.41  tff(c_859, plain, (![A_144, B_145, D_147]: (k7_relset_1(A_144, B_145, '#skF_4', D_147)=k9_relat_1('#skF_4', D_147))), inference(resolution, [status(thm)], [c_579, c_856])).
% 2.81/1.41  tff(c_861, plain, (![A_144, B_145, D_147]: (k7_relset_1(A_144, B_145, '#skF_4', D_147)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_859])).
% 2.81/1.41  tff(c_862, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_861, c_54])).
% 2.81/1.41  tff(c_865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_862])).
% 2.81/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  Inference rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Ref     : 0
% 2.81/1.41  #Sup     : 160
% 2.81/1.41  #Fact    : 0
% 2.81/1.41  #Define  : 0
% 2.81/1.41  #Split   : 3
% 2.81/1.41  #Chain   : 0
% 2.81/1.41  #Close   : 0
% 2.81/1.41  
% 2.81/1.41  Ordering : KBO
% 2.81/1.41  
% 2.81/1.41  Simplification rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Subsume      : 6
% 2.81/1.41  #Demod        : 161
% 2.81/1.41  #Tautology    : 114
% 2.81/1.41  #SimpNegUnit  : 3
% 2.81/1.41  #BackRed      : 18
% 2.81/1.41  
% 2.81/1.41  #Partial instantiations: 0
% 2.81/1.41  #Strategies tried      : 1
% 2.81/1.41  
% 2.81/1.41  Timing (in seconds)
% 2.81/1.41  ----------------------
% 2.81/1.41  Preprocessing        : 0.33
% 2.81/1.41  Parsing              : 0.18
% 2.81/1.41  CNF conversion       : 0.02
% 2.81/1.41  Main loop            : 0.32
% 2.81/1.41  Inferencing          : 0.11
% 2.81/1.41  Reduction            : 0.11
% 2.81/1.41  Demodulation         : 0.08
% 2.81/1.41  BG Simplification    : 0.02
% 2.81/1.41  Subsumption          : 0.06
% 2.81/1.41  Abstraction          : 0.01
% 2.81/1.41  MUC search           : 0.00
% 2.81/1.41  Cooper               : 0.00
% 2.81/1.41  Total                : 0.68
% 2.81/1.41  Index Insertion      : 0.00
% 2.81/1.41  Index Deletion       : 0.00
% 2.81/1.41  Index Matching       : 0.00
% 2.81/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
