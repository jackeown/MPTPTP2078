%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:38 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   68 (  80 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 123 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_46,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_73,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_79,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_83,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_22,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,C_13))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_243,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r1_tarski(k1_zfmisc_1(A_98),B_97)
      | ~ r1_tarski(C_96,A_98) ) ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_274,plain,(
    ! [C_105,B_106,A_107] :
      ( r2_hidden(C_105,k1_zfmisc_1(B_106))
      | ~ r1_tarski(C_105,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_24,c_243])).

tff(c_357,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_7',k1_zfmisc_1(B_117))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),B_117) ) ),
    inference(resolution,[status(thm)],[c_65,c_274])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_375,plain,(
    ! [B_120] :
      ( r1_tarski('#skF_7',B_120)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),B_120) ) ),
    inference(resolution,[status(thm)],[c_357,c_8])).

tff(c_392,plain,(
    ! [B_121] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(B_121,'#skF_4'))
      | ~ r1_tarski('#skF_5',B_121) ) ),
    inference(resolution,[status(thm)],[c_22,c_375])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    ! [A_16,A_58,B_59] :
      ( v4_relat_1(A_16,A_58)
      | ~ r1_tarski(A_16,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_28,c_116])).

tff(c_411,plain,(
    ! [B_122] :
      ( v4_relat_1('#skF_7',B_122)
      | ~ r1_tarski('#skF_5',B_122) ) ),
    inference(resolution,[status(thm)],[c_392,c_124])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_414,plain,(
    ! [B_122] :
      ( k7_relat_1('#skF_7',B_122) = '#skF_7'
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski('#skF_5',B_122) ) ),
    inference(resolution,[status(thm)],[c_411,c_34])).

tff(c_418,plain,(
    ! [B_123] :
      ( k7_relat_1('#skF_7',B_123) = '#skF_7'
      | ~ r1_tarski('#skF_5',B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_414])).

tff(c_432,plain,(
    k7_relat_1('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_418])).

tff(c_505,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k5_relset_1(A_131,B_132,C_133,D_134) = k7_relat_1(C_133,D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_512,plain,(
    ! [D_134] : k5_relset_1('#skF_5','#skF_4','#skF_7',D_134) = k7_relat_1('#skF_7',D_134) ),
    inference(resolution,[status(thm)],[c_48,c_505])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_5','#skF_4',k5_relset_1('#skF_5','#skF_4','#skF_7','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_513,plain,(
    ~ r2_relset_1('#skF_5','#skF_4',k7_relat_1('#skF_7','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_44])).

tff(c_514,plain,(
    ~ r2_relset_1('#skF_5','#skF_4','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_513])).

tff(c_611,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( r2_relset_1(A_154,B_155,C_156,C_156)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_619,plain,(
    ! [C_158] :
      ( r2_relset_1('#skF_5','#skF_4',C_158,C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_611])).

tff(c_624,plain,(
    r2_relset_1('#skF_5','#skF_4','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_619])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:01:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.96  
% 3.50/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.96  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.50/1.96  
% 3.50/1.96  %Foreground sorts:
% 3.50/1.96  
% 3.50/1.96  
% 3.50/1.96  %Background operators:
% 3.50/1.96  
% 3.50/1.96  
% 3.50/1.96  %Foreground operators:
% 3.50/1.96  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.50/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.50/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.50/1.96  tff('#skF_7', type, '#skF_7': $i).
% 3.50/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.50/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.96  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.96  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.50/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.96  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.50/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.96  
% 3.50/1.99  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 3.50/1.99  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.50/1.99  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.50/1.99  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.50/1.99  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.50/1.99  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.50/1.99  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.50/1.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.50/1.99  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.50/1.99  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.50/1.99  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.50/1.99  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.50/1.99  tff(c_46, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.50/1.99  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.50/1.99  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.50/1.99  tff(c_73, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.50/1.99  tff(c_79, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_73])).
% 3.50/1.99  tff(c_83, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 3.50/1.99  tff(c_22, plain, (![A_11, C_13, B_12]: (r1_tarski(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, C_13)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.99  tff(c_57, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.50/1.99  tff(c_65, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_57])).
% 3.50/1.99  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.50/1.99  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.50/1.99  tff(c_138, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.99  tff(c_243, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r1_tarski(k1_zfmisc_1(A_98), B_97) | ~r1_tarski(C_96, A_98))), inference(resolution, [status(thm)], [c_10, c_138])).
% 3.50/1.99  tff(c_274, plain, (![C_105, B_106, A_107]: (r2_hidden(C_105, k1_zfmisc_1(B_106)) | ~r1_tarski(C_105, A_107) | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_24, c_243])).
% 3.50/1.99  tff(c_357, plain, (![B_117]: (r2_hidden('#skF_7', k1_zfmisc_1(B_117)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), B_117))), inference(resolution, [status(thm)], [c_65, c_274])).
% 3.50/1.99  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.50/1.99  tff(c_375, plain, (![B_120]: (r1_tarski('#skF_7', B_120) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), B_120))), inference(resolution, [status(thm)], [c_357, c_8])).
% 3.50/1.99  tff(c_392, plain, (![B_121]: (r1_tarski('#skF_7', k2_zfmisc_1(B_121, '#skF_4')) | ~r1_tarski('#skF_5', B_121))), inference(resolution, [status(thm)], [c_22, c_375])).
% 3.50/1.99  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.50/1.99  tff(c_116, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.50/1.99  tff(c_124, plain, (![A_16, A_58, B_59]: (v4_relat_1(A_16, A_58) | ~r1_tarski(A_16, k2_zfmisc_1(A_58, B_59)))), inference(resolution, [status(thm)], [c_28, c_116])).
% 3.50/1.99  tff(c_411, plain, (![B_122]: (v4_relat_1('#skF_7', B_122) | ~r1_tarski('#skF_5', B_122))), inference(resolution, [status(thm)], [c_392, c_124])).
% 3.50/1.99  tff(c_34, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.50/1.99  tff(c_414, plain, (![B_122]: (k7_relat_1('#skF_7', B_122)='#skF_7' | ~v1_relat_1('#skF_7') | ~r1_tarski('#skF_5', B_122))), inference(resolution, [status(thm)], [c_411, c_34])).
% 3.50/1.99  tff(c_418, plain, (![B_123]: (k7_relat_1('#skF_7', B_123)='#skF_7' | ~r1_tarski('#skF_5', B_123))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_414])).
% 3.50/1.99  tff(c_432, plain, (k7_relat_1('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_46, c_418])).
% 3.50/1.99  tff(c_505, plain, (![A_131, B_132, C_133, D_134]: (k5_relset_1(A_131, B_132, C_133, D_134)=k7_relat_1(C_133, D_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.50/1.99  tff(c_512, plain, (![D_134]: (k5_relset_1('#skF_5', '#skF_4', '#skF_7', D_134)=k7_relat_1('#skF_7', D_134))), inference(resolution, [status(thm)], [c_48, c_505])).
% 3.50/1.99  tff(c_44, plain, (~r2_relset_1('#skF_5', '#skF_4', k5_relset_1('#skF_5', '#skF_4', '#skF_7', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.50/1.99  tff(c_513, plain, (~r2_relset_1('#skF_5', '#skF_4', k7_relat_1('#skF_7', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_44])).
% 3.50/1.99  tff(c_514, plain, (~r2_relset_1('#skF_5', '#skF_4', '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_513])).
% 3.50/1.99  tff(c_611, plain, (![A_154, B_155, C_156, D_157]: (r2_relset_1(A_154, B_155, C_156, C_156) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.50/1.99  tff(c_619, plain, (![C_158]: (r2_relset_1('#skF_5', '#skF_4', C_158, C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(resolution, [status(thm)], [c_48, c_611])).
% 3.50/1.99  tff(c_624, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_619])).
% 3.50/1.99  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_624])).
% 3.50/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.99  
% 3.50/1.99  Inference rules
% 3.50/1.99  ----------------------
% 3.50/1.99  #Ref     : 0
% 3.50/1.99  #Sup     : 124
% 3.50/1.99  #Fact    : 0
% 3.50/1.99  #Define  : 0
% 3.50/1.99  #Split   : 4
% 3.50/1.99  #Chain   : 0
% 3.50/1.99  #Close   : 0
% 3.50/1.99  
% 3.50/1.99  Ordering : KBO
% 3.50/1.99  
% 3.50/1.99  Simplification rules
% 3.50/1.99  ----------------------
% 3.50/1.99  #Subsume      : 9
% 3.50/1.99  #Demod        : 29
% 3.50/1.99  #Tautology    : 32
% 3.50/1.99  #SimpNegUnit  : 1
% 3.50/1.99  #BackRed      : 1
% 3.50/1.99  
% 3.50/1.99  #Partial instantiations: 0
% 3.50/1.99  #Strategies tried      : 1
% 3.50/1.99  
% 3.50/1.99  Timing (in seconds)
% 3.50/1.99  ----------------------
% 3.78/1.99  Preprocessing        : 0.52
% 3.78/1.99  Parsing              : 0.26
% 3.78/1.99  CNF conversion       : 0.04
% 3.78/1.99  Main loop            : 0.57
% 3.78/1.99  Inferencing          : 0.21
% 3.78/1.99  Reduction            : 0.16
% 3.78/1.99  Demodulation         : 0.11
% 3.78/1.99  BG Simplification    : 0.03
% 3.78/1.99  Subsumption          : 0.12
% 3.78/1.99  Abstraction          : 0.03
% 3.78/1.99  MUC search           : 0.00
% 3.78/1.99  Cooper               : 0.00
% 3.78/2.00  Total                : 1.14
% 3.78/2.00  Index Insertion      : 0.00
% 3.78/2.00  Index Deletion       : 0.00
% 3.78/2.00  Index Matching       : 0.00
% 3.78/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
