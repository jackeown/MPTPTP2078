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
% DateTime   : Thu Dec  3 10:07:37 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 160 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 298 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_150,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_153,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).

tff(c_59,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_78,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,A_49) = B_48
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_78])).

tff(c_84,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_81])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r1_tarski(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_54,plain,(
    ! [B_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_88,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_54])).

tff(c_95,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_88])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_378,plain,(
    ! [C_97,A_98,B_99] :
      ( m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ r1_tarski(k2_relat_1(C_97),B_99)
      | ~ r1_tarski(k1_relat_1(C_97),A_98)
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [C_17,A_15,B_16] :
      ( v4_relat_1(C_17,A_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_399,plain,(
    ! [C_100,A_101,B_102] :
      ( v4_relat_1(C_100,A_101)
      | ~ r1_tarski(k2_relat_1(C_100),B_102)
      | ~ r1_tarski(k1_relat_1(C_100),A_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_378,c_18])).

tff(c_406,plain,(
    ! [B_103,A_104,A_105] :
      ( v4_relat_1(B_103,A_104)
      | ~ r1_tarski(k1_relat_1(B_103),A_104)
      | ~ v5_relat_1(B_103,A_105)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_8,c_399])).

tff(c_422,plain,(
    ! [A_105] :
      ( v4_relat_1('#skF_4','#skF_3')
      | ~ v5_relat_1('#skF_4',A_105)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_95,c_406])).

tff(c_438,plain,(
    ! [A_105] :
      ( v4_relat_1('#skF_4','#skF_3')
      | ~ v5_relat_1('#skF_4',A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_422])).

tff(c_441,plain,(
    ! [A_105] : ~ v5_relat_1('#skF_4',A_105) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_64,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_68])).

tff(c_444,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_447,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_444,c_12])).

tff(c_450,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_447])).

tff(c_227,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k5_relset_1(A_75,B_76,C_77,D_78) = k7_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_230,plain,(
    ! [D_78] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_78) = k7_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_32,c_227])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_231,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_28])).

tff(c_451,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_231])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.94  
% 3.33/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.95  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.95  
% 3.33/1.95  %Foreground sorts:
% 3.33/1.95  
% 3.33/1.95  
% 3.33/1.95  %Background operators:
% 3.33/1.95  
% 3.33/1.95  
% 3.33/1.95  %Foreground operators:
% 3.33/1.95  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.33/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.33/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.33/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.33/1.95  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.95  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.95  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.95  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.95  
% 3.33/1.98  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 3.33/1.98  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.33/1.98  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.33/1.98  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.33/1.98  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.98  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.33/1.98  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.33/1.98  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.33/1.98  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.33/1.98  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.33/1.98  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.33/1.98  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.98  tff(c_150, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.33/1.98  tff(c_153, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_150])).
% 3.33/1.98  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.98  tff(c_35, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.33/1.98  tff(c_38, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_35])).
% 3.33/1.98  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 3.33/1.98  tff(c_59, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.33/1.98  tff(c_63, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_59])).
% 3.33/1.98  tff(c_78, plain, (![B_48, A_49]: (k7_relat_1(B_48, A_49)=B_48 | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.33/1.98  tff(c_81, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_78])).
% 3.33/1.98  tff(c_84, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_81])).
% 3.33/1.98  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.98  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.98  tff(c_42, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.98  tff(c_49, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r1_tarski(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_42])).
% 3.33/1.98  tff(c_54, plain, (![B_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, '#skF_2')), '#skF_3') | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_14, c_49])).
% 3.33/1.98  tff(c_88, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_84, c_54])).
% 3.33/1.98  tff(c_95, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_88])).
% 3.33/1.98  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.98  tff(c_378, plain, (![C_97, A_98, B_99]: (m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~r1_tarski(k2_relat_1(C_97), B_99) | ~r1_tarski(k1_relat_1(C_97), A_98) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.33/1.98  tff(c_18, plain, (![C_17, A_15, B_16]: (v4_relat_1(C_17, A_15) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.33/1.98  tff(c_399, plain, (![C_100, A_101, B_102]: (v4_relat_1(C_100, A_101) | ~r1_tarski(k2_relat_1(C_100), B_102) | ~r1_tarski(k1_relat_1(C_100), A_101) | ~v1_relat_1(C_100))), inference(resolution, [status(thm)], [c_378, c_18])).
% 3.33/1.98  tff(c_406, plain, (![B_103, A_104, A_105]: (v4_relat_1(B_103, A_104) | ~r1_tarski(k1_relat_1(B_103), A_104) | ~v5_relat_1(B_103, A_105) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_8, c_399])).
% 3.33/1.98  tff(c_422, plain, (![A_105]: (v4_relat_1('#skF_4', '#skF_3') | ~v5_relat_1('#skF_4', A_105) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_95, c_406])).
% 3.33/1.98  tff(c_438, plain, (![A_105]: (v4_relat_1('#skF_4', '#skF_3') | ~v5_relat_1('#skF_4', A_105))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_422])).
% 3.33/1.98  tff(c_441, plain, (![A_105]: (~v5_relat_1('#skF_4', A_105))), inference(splitLeft, [status(thm)], [c_438])).
% 3.33/1.98  tff(c_64, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.33/1.98  tff(c_68, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_64])).
% 3.33/1.98  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_68])).
% 3.33/1.98  tff(c_444, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_438])).
% 3.33/1.98  tff(c_12, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.33/1.98  tff(c_447, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_444, c_12])).
% 3.33/1.98  tff(c_450, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_447])).
% 3.33/1.98  tff(c_227, plain, (![A_75, B_76, C_77, D_78]: (k5_relset_1(A_75, B_76, C_77, D_78)=k7_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.33/1.98  tff(c_230, plain, (![D_78]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_78)=k7_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_32, c_227])).
% 3.33/1.98  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.98  tff(c_231, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_28])).
% 3.33/1.98  tff(c_451, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_231])).
% 3.33/1.98  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_451])).
% 3.33/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.98  
% 3.33/1.98  Inference rules
% 3.33/1.98  ----------------------
% 3.33/1.98  #Ref     : 0
% 3.33/1.98  #Sup     : 89
% 3.33/1.98  #Fact    : 0
% 3.33/1.98  #Define  : 0
% 3.33/1.98  #Split   : 1
% 3.33/1.98  #Chain   : 0
% 3.33/1.98  #Close   : 0
% 3.33/1.98  
% 3.33/1.98  Ordering : KBO
% 3.33/1.98  
% 3.33/1.98  Simplification rules
% 3.33/1.98  ----------------------
% 3.33/1.98  #Subsume      : 10
% 3.33/1.98  #Demod        : 19
% 3.33/1.98  #Tautology    : 8
% 3.33/1.98  #SimpNegUnit  : 1
% 3.33/1.98  #BackRed      : 3
% 3.33/1.98  
% 3.33/1.98  #Partial instantiations: 0
% 3.33/1.98  #Strategies tried      : 1
% 3.33/1.98  
% 3.33/1.98  Timing (in seconds)
% 3.33/1.98  ----------------------
% 3.42/1.99  Preprocessing        : 0.47
% 3.42/1.99  Parsing              : 0.25
% 3.42/1.99  CNF conversion       : 0.03
% 3.42/1.99  Main loop            : 0.61
% 3.42/1.99  Inferencing          : 0.23
% 3.42/1.99  Reduction            : 0.14
% 3.42/1.99  Demodulation         : 0.10
% 3.42/1.99  BG Simplification    : 0.02
% 3.42/1.99  Subsumption          : 0.16
% 3.42/1.99  Abstraction          : 0.04
% 3.42/1.99  MUC search           : 0.00
% 3.42/1.99  Cooper               : 0.00
% 3.42/1.99  Total                : 1.14
% 3.42/1.99  Index Insertion      : 0.00
% 3.42/1.99  Index Deletion       : 0.00
% 3.42/1.99  Index Matching       : 0.00
% 3.42/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
