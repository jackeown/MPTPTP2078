%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 187 expanded)
%              Number of leaves         :   38 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 378 expanded)
%              Number of equality atoms :   57 ( 115 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_123,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,A_15),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) = k1_xboole_0
      | k1_relat_1(A_17) != k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_135,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_127,c_34])).

tff(c_137,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_208,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(k1_funct_1(B_72,A_73)) = k2_relat_1(B_72)
      | k1_tarski(A_73) != k1_relat_1(B_72)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_220,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_46])).

tff(c_232,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_54,c_220])).

tff(c_234,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_148,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_152,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_148])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_283,plain,(
    ! [B_89,C_90,A_91] :
      ( k2_tarski(B_89,C_90) = A_91
      | k1_tarski(C_90) = A_91
      | k1_tarski(B_89) = A_91
      | k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k2_tarski(B_89,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_302,plain,(
    ! [A_4,A_91] :
      ( k2_tarski(A_4,A_4) = A_91
      | k1_tarski(A_4) = A_91
      | k1_tarski(A_4) = A_91
      | k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_283])).

tff(c_323,plain,(
    ! [A_92,A_93] :
      ( k1_tarski(A_92) = A_93
      | k1_tarski(A_92) = A_93
      | k1_tarski(A_92) = A_93
      | k1_xboole_0 = A_93
      | ~ r1_tarski(A_93,k1_tarski(A_92)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_302])).

tff(c_348,plain,(
    ! [A_94,B_95] :
      ( k1_tarski(A_94) = k1_relat_1(B_95)
      | k1_relat_1(B_95) = k1_xboole_0
      | ~ v4_relat_1(B_95,k1_tarski(A_94))
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_28,c_323])).

tff(c_354,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_348])).

tff(c_357,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_354])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_234,c_357])).

tff(c_361,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_364,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_50])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k7_relset_1(A_26,B_27,C_28,D_29) = k9_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_438,plain,(
    ! [D_29] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_29) = k9_relat_1('#skF_4',D_29) ),
    inference(resolution,[status(thm)],[c_364,c_44])).

tff(c_360,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_445,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_360])).

tff(c_446,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_445])).

tff(c_464,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_446])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_464])).

tff(c_469,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_32,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) = k1_xboole_0
      | k2_relat_1(A_17) != k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_134,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_136,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_136])).

tff(c_487,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_500,plain,(
    ! [A_15] :
      ( r1_tarski(k9_relat_1('#skF_4',A_15),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_30])).

tff(c_506,plain,(
    ! [A_108] : r1_tarski(k9_relat_1('#skF_4',A_108),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_500])).

tff(c_90,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_512,plain,(
    ! [A_108] : k9_relat_1('#skF_4',A_108) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_506,c_108])).

tff(c_637,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k7_relset_1(A_131,B_132,C_133,D_134) = k9_relat_1(C_133,D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_639,plain,(
    ! [D_134] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_134) = k9_relat_1('#skF_4',D_134) ),
    inference(resolution,[status(thm)],[c_50,c_637])).

tff(c_641,plain,(
    ! [D_134] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_134) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_639])).

tff(c_668,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_46])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.80/1.41  
% 2.80/1.41  %Foreground sorts:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Background operators:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Foreground operators:
% 2.80/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.80/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.80/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.80/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.41  
% 2.80/1.42  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.42  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.80/1.42  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.80/1.42  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.80/1.42  tff(f_70, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.80/1.42  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.80/1.42  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.80/1.42  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.80/1.42  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.42  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.80/1.42  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.80/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.42  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.42  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.42  tff(c_123, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.42  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_123])).
% 2.80/1.42  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, A_15), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.80/1.42  tff(c_34, plain, (![A_17]: (k2_relat_1(A_17)=k1_xboole_0 | k1_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.42  tff(c_135, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_127, c_34])).
% 2.80/1.42  tff(c_137, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_135])).
% 2.80/1.42  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.42  tff(c_208, plain, (![B_72, A_73]: (k1_tarski(k1_funct_1(B_72, A_73))=k2_relat_1(B_72) | k1_tarski(A_73)!=k1_relat_1(B_72) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.42  tff(c_46, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.42  tff(c_220, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_208, c_46])).
% 2.80/1.42  tff(c_232, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_54, c_220])).
% 2.80/1.42  tff(c_234, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_232])).
% 2.80/1.42  tff(c_148, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.80/1.42  tff(c_152, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_148])).
% 2.80/1.42  tff(c_28, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.80/1.42  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.42  tff(c_283, plain, (![B_89, C_90, A_91]: (k2_tarski(B_89, C_90)=A_91 | k1_tarski(C_90)=A_91 | k1_tarski(B_89)=A_91 | k1_xboole_0=A_91 | ~r1_tarski(A_91, k2_tarski(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.80/1.42  tff(c_302, plain, (![A_4, A_91]: (k2_tarski(A_4, A_4)=A_91 | k1_tarski(A_4)=A_91 | k1_tarski(A_4)=A_91 | k1_xboole_0=A_91 | ~r1_tarski(A_91, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_283])).
% 2.80/1.42  tff(c_323, plain, (![A_92, A_93]: (k1_tarski(A_92)=A_93 | k1_tarski(A_92)=A_93 | k1_tarski(A_92)=A_93 | k1_xboole_0=A_93 | ~r1_tarski(A_93, k1_tarski(A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_302])).
% 2.80/1.42  tff(c_348, plain, (![A_94, B_95]: (k1_tarski(A_94)=k1_relat_1(B_95) | k1_relat_1(B_95)=k1_xboole_0 | ~v4_relat_1(B_95, k1_tarski(A_94)) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_28, c_323])).
% 2.80/1.42  tff(c_354, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_152, c_348])).
% 2.80/1.42  tff(c_357, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_127, c_354])).
% 2.80/1.42  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_234, c_357])).
% 2.80/1.42  tff(c_361, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_232])).
% 2.80/1.42  tff(c_364, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_50])).
% 2.80/1.42  tff(c_44, plain, (![A_26, B_27, C_28, D_29]: (k7_relset_1(A_26, B_27, C_28, D_29)=k9_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.42  tff(c_438, plain, (![D_29]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_29)=k9_relat_1('#skF_4', D_29))), inference(resolution, [status(thm)], [c_364, c_44])).
% 2.80/1.42  tff(c_360, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_232])).
% 2.80/1.42  tff(c_445, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_360])).
% 2.80/1.42  tff(c_446, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_445])).
% 2.80/1.42  tff(c_464, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_446])).
% 2.80/1.42  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_464])).
% 2.80/1.42  tff(c_469, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_135])).
% 2.80/1.42  tff(c_32, plain, (![A_17]: (k1_relat_1(A_17)=k1_xboole_0 | k2_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.42  tff(c_134, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_127, c_32])).
% 2.80/1.42  tff(c_136, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 2.80/1.42  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_136])).
% 2.80/1.42  tff(c_487, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 2.80/1.42  tff(c_500, plain, (![A_15]: (r1_tarski(k9_relat_1('#skF_4', A_15), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_30])).
% 2.80/1.42  tff(c_506, plain, (![A_108]: (r1_tarski(k9_relat_1('#skF_4', A_108), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_500])).
% 2.80/1.42  tff(c_90, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.42  tff(c_108, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_90])).
% 2.80/1.42  tff(c_512, plain, (![A_108]: (k9_relat_1('#skF_4', A_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_506, c_108])).
% 2.80/1.42  tff(c_637, plain, (![A_131, B_132, C_133, D_134]: (k7_relset_1(A_131, B_132, C_133, D_134)=k9_relat_1(C_133, D_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.42  tff(c_639, plain, (![D_134]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_134)=k9_relat_1('#skF_4', D_134))), inference(resolution, [status(thm)], [c_50, c_637])).
% 2.80/1.42  tff(c_641, plain, (![D_134]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_134)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_512, c_639])).
% 2.80/1.42  tff(c_668, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_46])).
% 2.80/1.42  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_668])).
% 2.80/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  Inference rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Ref     : 0
% 2.80/1.42  #Sup     : 127
% 2.80/1.42  #Fact    : 0
% 2.80/1.42  #Define  : 0
% 2.80/1.42  #Split   : 3
% 2.80/1.42  #Chain   : 0
% 2.80/1.42  #Close   : 0
% 2.80/1.42  
% 2.80/1.42  Ordering : KBO
% 2.80/1.42  
% 2.80/1.42  Simplification rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Subsume      : 9
% 2.80/1.42  #Demod        : 88
% 2.80/1.42  #Tautology    : 69
% 2.80/1.42  #SimpNegUnit  : 1
% 2.80/1.42  #BackRed      : 8
% 2.80/1.42  
% 2.80/1.42  #Partial instantiations: 0
% 2.80/1.42  #Strategies tried      : 1
% 2.80/1.42  
% 2.80/1.42  Timing (in seconds)
% 2.80/1.42  ----------------------
% 2.80/1.42  Preprocessing        : 0.32
% 2.80/1.42  Parsing              : 0.17
% 2.80/1.42  CNF conversion       : 0.02
% 2.80/1.43  Main loop            : 0.30
% 2.80/1.43  Inferencing          : 0.11
% 2.80/1.43  Reduction            : 0.10
% 2.80/1.43  Demodulation         : 0.07
% 2.80/1.43  BG Simplification    : 0.02
% 2.80/1.43  Subsumption          : 0.05
% 2.80/1.43  Abstraction          : 0.01
% 2.80/1.43  MUC search           : 0.00
% 2.80/1.43  Cooper               : 0.00
% 2.80/1.43  Total                : 0.66
% 2.80/1.43  Index Insertion      : 0.00
% 2.80/1.43  Index Deletion       : 0.00
% 2.80/1.43  Index Matching       : 0.00
% 2.80/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
