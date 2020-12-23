%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 224 expanded)
%              Number of leaves         :   39 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 445 expanded)
%              Number of equality atoms :   45 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_71,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_76,plain,(
    ! [A_41] :
      ( k1_relat_1(A_41) = k1_xboole_0
      | k2_relat_1(A_41) != k1_xboole_0
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_76])).

tff(c_81,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_82,plain,(
    ! [A_42] :
      ( k2_relat_1(A_42) = k1_xboole_0
      | k1_relat_1(A_42) != k1_xboole_0
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_85,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_82])).

tff(c_88,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_85])).

tff(c_102,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_116,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(k1_relat_1(B_53),A_54)
      | ~ v4_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(B_9) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_168,plain,(
    ! [B_62,B_63] :
      ( k1_tarski(B_62) = k1_relat_1(B_63)
      | k1_relat_1(B_63) = k1_xboole_0
      | ~ v4_relat_1(B_63,k1_tarski(B_62))
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_116,c_10])).

tff(c_171,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_168])).

tff(c_174,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_171])).

tff(c_175,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_174])).

tff(c_285,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(k1_funct_1(B_70,A_71)) = k2_relat_1(B_70)
      | k1_tarski(A_71) != k1_relat_1(B_70)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_180,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_44])).

tff(c_38,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k7_relset_1(A_27,B_28,C_29,D_30) = k9_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_237,plain,(
    ! [D_30] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_30) = k9_relat_1('#skF_4',D_30) ),
    inference(resolution,[status(thm)],[c_180,c_38])).

tff(c_40,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_179,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_40])).

tff(c_284,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_179])).

tff(c_291,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_284])).

tff(c_309,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_175,c_291])).

tff(c_313,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_309])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_313])).

tff(c_319,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_318,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_341,plain,(
    ! [B_74,A_75] :
      ( v4_relat_1(B_74,A_75)
      | ~ r1_tarski(k1_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_344,plain,(
    ! [A_75] :
      ( v4_relat_1('#skF_4',A_75)
      | ~ r1_tarski(k1_xboole_0,A_75)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_341])).

tff(c_346,plain,(
    ! [A_75] : v4_relat_1('#skF_4',A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2,c_344])).

tff(c_387,plain,(
    ! [B_87,A_88] :
      ( k7_relat_1(B_87,A_88) = B_87
      | ~ v4_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_390,plain,(
    ! [A_75] :
      ( k7_relat_1('#skF_4',A_75) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_346,c_387])).

tff(c_394,plain,(
    ! [A_89] : k7_relat_1('#skF_4',A_89) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_390])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_399,plain,(
    ! [A_89] :
      ( k9_relat_1('#skF_4',A_89) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_22])).

tff(c_404,plain,(
    ! [A_89] : k9_relat_1('#skF_4',A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_319,c_399])).

tff(c_474,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_476,plain,(
    ! [D_103] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_103) = k9_relat_1('#skF_4',D_103) ),
    inference(resolution,[status(thm)],[c_44,c_474])).

tff(c_478,plain,(
    ! [D_103] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_476])).

tff(c_479,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_40])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.31  
% 2.27/1.31  %Foreground sorts:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Background operators:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Foreground operators:
% 2.27/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.27/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.31  
% 2.27/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.27/1.32  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.27/1.32  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.27/1.32  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.27/1.32  tff(f_65, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.27/1.32  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.32  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.27/1.32  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.27/1.32  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.27/1.32  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.27/1.32  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.27/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.27/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.32  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.27/1.32  tff(c_71, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.27/1.32  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 2.27/1.32  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, A_12), k2_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.32  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.27/1.32  tff(c_76, plain, (![A_41]: (k1_relat_1(A_41)=k1_xboole_0 | k2_relat_1(A_41)!=k1_xboole_0 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.32  tff(c_80, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_76])).
% 2.27/1.32  tff(c_81, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80])).
% 2.27/1.32  tff(c_82, plain, (![A_42]: (k2_relat_1(A_42)=k1_xboole_0 | k1_relat_1(A_42)!=k1_xboole_0 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.32  tff(c_85, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_82])).
% 2.27/1.32  tff(c_88, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_81, c_85])).
% 2.27/1.32  tff(c_102, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.32  tff(c_106, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_102])).
% 2.27/1.32  tff(c_116, plain, (![B_53, A_54]: (r1_tarski(k1_relat_1(B_53), A_54) | ~v4_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.32  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(B_9)=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.32  tff(c_168, plain, (![B_62, B_63]: (k1_tarski(B_62)=k1_relat_1(B_63) | k1_relat_1(B_63)=k1_xboole_0 | ~v4_relat_1(B_63, k1_tarski(B_62)) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_116, c_10])).
% 2.27/1.32  tff(c_171, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_168])).
% 2.27/1.32  tff(c_174, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_75, c_171])).
% 2.27/1.32  tff(c_175, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_88, c_174])).
% 2.27/1.32  tff(c_285, plain, (![B_70, A_71]: (k1_tarski(k1_funct_1(B_70, A_71))=k2_relat_1(B_70) | k1_tarski(A_71)!=k1_relat_1(B_70) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.27/1.32  tff(c_180, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_44])).
% 2.27/1.32  tff(c_38, plain, (![A_27, B_28, C_29, D_30]: (k7_relset_1(A_27, B_28, C_29, D_30)=k9_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.32  tff(c_237, plain, (![D_30]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_30)=k9_relat_1('#skF_4', D_30))), inference(resolution, [status(thm)], [c_180, c_38])).
% 2.27/1.32  tff(c_40, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.27/1.32  tff(c_179, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_40])).
% 2.27/1.32  tff(c_284, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_179])).
% 2.27/1.32  tff(c_291, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_285, c_284])).
% 2.27/1.32  tff(c_309, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_175, c_291])).
% 2.27/1.32  tff(c_313, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_309])).
% 2.27/1.32  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_313])).
% 2.27/1.32  tff(c_319, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_80])).
% 2.27/1.32  tff(c_318, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_80])).
% 2.27/1.32  tff(c_341, plain, (![B_74, A_75]: (v4_relat_1(B_74, A_75) | ~r1_tarski(k1_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.32  tff(c_344, plain, (![A_75]: (v4_relat_1('#skF_4', A_75) | ~r1_tarski(k1_xboole_0, A_75) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_341])).
% 2.27/1.32  tff(c_346, plain, (![A_75]: (v4_relat_1('#skF_4', A_75))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2, c_344])).
% 2.27/1.32  tff(c_387, plain, (![B_87, A_88]: (k7_relat_1(B_87, A_88)=B_87 | ~v4_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.32  tff(c_390, plain, (![A_75]: (k7_relat_1('#skF_4', A_75)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_346, c_387])).
% 2.27/1.32  tff(c_394, plain, (![A_89]: (k7_relat_1('#skF_4', A_89)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_390])).
% 2.27/1.32  tff(c_22, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.32  tff(c_399, plain, (![A_89]: (k9_relat_1('#skF_4', A_89)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_394, c_22])).
% 2.27/1.32  tff(c_404, plain, (![A_89]: (k9_relat_1('#skF_4', A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_319, c_399])).
% 2.27/1.32  tff(c_474, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.32  tff(c_476, plain, (![D_103]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_103)=k9_relat_1('#skF_4', D_103))), inference(resolution, [status(thm)], [c_44, c_474])).
% 2.27/1.32  tff(c_478, plain, (![D_103]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_404, c_476])).
% 2.27/1.32  tff(c_479, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_40])).
% 2.27/1.32  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_479])).
% 2.27/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  Inference rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Ref     : 0
% 2.27/1.32  #Sup     : 92
% 2.27/1.32  #Fact    : 0
% 2.27/1.32  #Define  : 0
% 2.27/1.32  #Split   : 1
% 2.27/1.32  #Chain   : 0
% 2.27/1.32  #Close   : 0
% 2.27/1.32  
% 2.27/1.33  Ordering : KBO
% 2.27/1.33  
% 2.27/1.33  Simplification rules
% 2.27/1.33  ----------------------
% 2.27/1.33  #Subsume      : 0
% 2.27/1.33  #Demod        : 58
% 2.27/1.33  #Tautology    : 59
% 2.27/1.33  #SimpNegUnit  : 4
% 2.27/1.33  #BackRed      : 8
% 2.27/1.33  
% 2.27/1.33  #Partial instantiations: 0
% 2.27/1.33  #Strategies tried      : 1
% 2.27/1.33  
% 2.27/1.33  Timing (in seconds)
% 2.27/1.33  ----------------------
% 2.27/1.33  Preprocessing        : 0.32
% 2.27/1.33  Parsing              : 0.17
% 2.27/1.33  CNF conversion       : 0.02
% 2.27/1.33  Main loop            : 0.24
% 2.27/1.33  Inferencing          : 0.09
% 2.27/1.33  Reduction            : 0.08
% 2.27/1.33  Demodulation         : 0.06
% 2.27/1.33  BG Simplification    : 0.02
% 2.27/1.33  Subsumption          : 0.03
% 2.27/1.33  Abstraction          : 0.01
% 2.27/1.33  MUC search           : 0.00
% 2.27/1.33  Cooper               : 0.00
% 2.27/1.33  Total                : 0.60
% 2.27/1.33  Index Insertion      : 0.00
% 2.27/1.33  Index Deletion       : 0.00
% 2.27/1.33  Index Matching       : 0.00
% 2.27/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
