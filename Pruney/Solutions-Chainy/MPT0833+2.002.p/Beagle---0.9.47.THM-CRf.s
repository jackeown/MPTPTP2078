%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   67 (  77 expanded)
%              Number of leaves         :   34 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 122 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_212,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_relset_1(A_89,B_90,C_91,C_91)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_220,plain,(
    ! [C_93] :
      ( r2_relset_1('#skF_2','#skF_3',C_93,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_212])).

tff(c_227,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_220])).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k2_zfmisc_1(C_8,A_6),k2_zfmisc_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_zfmisc_1(A_9),k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_177,plain,(
    ! [A_83,B_84,B_85] :
      ( r2_hidden(A_83,B_84)
      | ~ r1_tarski(B_85,B_84)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_83,B_85) ) ),
    inference(resolution,[status(thm)],[c_18,c_87])).

tff(c_185,plain,(
    ! [A_83,B_10,A_9] :
      ( r2_hidden(A_83,k1_zfmisc_1(B_10))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_83,k1_zfmisc_1(A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_177])).

tff(c_262,plain,(
    ! [A_99,B_100,A_101] :
      ( r2_hidden(A_99,k1_zfmisc_1(B_100))
      | ~ m1_subset_1(A_99,k1_zfmisc_1(A_101))
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_185])).

tff(c_274,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_5',k1_zfmisc_1(B_102))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_102) ) ),
    inference(resolution,[status(thm)],[c_40,c_262])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [B_103] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_103))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_103) ) ),
    inference(resolution,[status(thm)],[c_274,c_16])).

tff(c_331,plain,(
    ! [B_109] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_109)))
      | ~ r1_tarski('#skF_3',B_109) ) ),
    inference(resolution,[status(thm)],[c_8,c_282])).

tff(c_28,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_361,plain,(
    ! [B_110] :
      ( v5_relat_1('#skF_5',B_110)
      | ~ r1_tarski('#skF_3',B_110) ) ),
    inference(resolution,[status(thm)],[c_331,c_28])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [A_71,B_72] :
      ( k8_relat_1(A_71,B_72) = B_72
      | ~ r1_tarski(k2_relat_1(B_72),A_71)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_126,plain,(
    ! [A_16,B_17] :
      ( k8_relat_1(A_16,B_17) = B_17
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_364,plain,(
    ! [B_110] :
      ( k8_relat_1(B_110,'#skF_5') = '#skF_5'
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_110) ) ),
    inference(resolution,[status(thm)],[c_361,c_126])).

tff(c_368,plain,(
    ! [B_111] :
      ( k8_relat_1(B_111,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_3',B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_364])).

tff(c_378,plain,(
    k8_relat_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_368])).

tff(c_137,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k6_relset_1(A_74,B_75,C_76,D_77) = k8_relat_1(C_76,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_144,plain,(
    ! [C_76] : k6_relset_1('#skF_2','#skF_3',C_76,'#skF_5') = k8_relat_1(C_76,'#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k6_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_145,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k8_relat_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_36])).

tff(c_379,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_145])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:47:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.58/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.35  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.58/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.58/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.35  
% 2.58/1.37  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.58/1.37  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.58/1.37  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.37  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.58/1.37  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.58/1.37  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.58/1.37  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.58/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.58/1.37  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.58/1.37  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.37  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.58/1.37  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.58/1.37  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.58/1.37  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.37  tff(c_212, plain, (![A_89, B_90, C_91, D_92]: (r2_relset_1(A_89, B_90, C_91, C_91) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.58/1.37  tff(c_220, plain, (![C_93]: (r2_relset_1('#skF_2', '#skF_3', C_93, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_40, c_212])).
% 2.58/1.37  tff(c_227, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_220])).
% 2.58/1.37  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.37  tff(c_44, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.37  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_44])).
% 2.58/1.37  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k2_zfmisc_1(C_8, A_6), k2_zfmisc_1(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.37  tff(c_14, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.37  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_zfmisc_1(A_9), k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.37  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.58/1.37  tff(c_87, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.37  tff(c_177, plain, (![A_83, B_84, B_85]: (r2_hidden(A_83, B_84) | ~r1_tarski(B_85, B_84) | v1_xboole_0(B_85) | ~m1_subset_1(A_83, B_85))), inference(resolution, [status(thm)], [c_18, c_87])).
% 2.58/1.37  tff(c_185, plain, (![A_83, B_10, A_9]: (r2_hidden(A_83, k1_zfmisc_1(B_10)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~m1_subset_1(A_83, k1_zfmisc_1(A_9)) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_177])).
% 2.58/1.37  tff(c_262, plain, (![A_99, B_100, A_101]: (r2_hidden(A_99, k1_zfmisc_1(B_100)) | ~m1_subset_1(A_99, k1_zfmisc_1(A_101)) | ~r1_tarski(A_101, B_100))), inference(negUnitSimplification, [status(thm)], [c_14, c_185])).
% 2.58/1.37  tff(c_274, plain, (![B_102]: (r2_hidden('#skF_5', k1_zfmisc_1(B_102)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_102))), inference(resolution, [status(thm)], [c_40, c_262])).
% 2.58/1.37  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.37  tff(c_282, plain, (![B_103]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_103)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_103))), inference(resolution, [status(thm)], [c_274, c_16])).
% 2.58/1.37  tff(c_331, plain, (![B_109]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_109))) | ~r1_tarski('#skF_3', B_109))), inference(resolution, [status(thm)], [c_8, c_282])).
% 2.58/1.37  tff(c_28, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.37  tff(c_361, plain, (![B_110]: (v5_relat_1('#skF_5', B_110) | ~r1_tarski('#skF_3', B_110))), inference(resolution, [status(thm)], [c_331, c_28])).
% 2.58/1.37  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.37  tff(c_118, plain, (![A_71, B_72]: (k8_relat_1(A_71, B_72)=B_72 | ~r1_tarski(k2_relat_1(B_72), A_71) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.37  tff(c_126, plain, (![A_16, B_17]: (k8_relat_1(A_16, B_17)=B_17 | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_22, c_118])).
% 2.58/1.37  tff(c_364, plain, (![B_110]: (k8_relat_1(B_110, '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_110))), inference(resolution, [status(thm)], [c_361, c_126])).
% 2.58/1.37  tff(c_368, plain, (![B_111]: (k8_relat_1(B_111, '#skF_5')='#skF_5' | ~r1_tarski('#skF_3', B_111))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_364])).
% 2.58/1.37  tff(c_378, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_38, c_368])).
% 2.58/1.37  tff(c_137, plain, (![A_74, B_75, C_76, D_77]: (k6_relset_1(A_74, B_75, C_76, D_77)=k8_relat_1(C_76, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.37  tff(c_144, plain, (![C_76]: (k6_relset_1('#skF_2', '#skF_3', C_76, '#skF_5')=k8_relat_1(C_76, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_137])).
% 2.58/1.37  tff(c_36, plain, (~r2_relset_1('#skF_2', '#skF_3', k6_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.37  tff(c_145, plain, (~r2_relset_1('#skF_2', '#skF_3', k8_relat_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_36])).
% 2.58/1.37  tff(c_379, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_145])).
% 2.58/1.37  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_379])).
% 2.58/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  Inference rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Ref     : 0
% 2.58/1.37  #Sup     : 72
% 2.58/1.37  #Fact    : 0
% 2.58/1.37  #Define  : 0
% 2.58/1.37  #Split   : 1
% 2.58/1.37  #Chain   : 0
% 2.58/1.37  #Close   : 0
% 2.58/1.37  
% 2.58/1.37  Ordering : KBO
% 2.58/1.37  
% 2.58/1.37  Simplification rules
% 2.58/1.37  ----------------------
% 2.58/1.37  #Subsume      : 2
% 2.58/1.37  #Demod        : 16
% 2.58/1.37  #Tautology    : 19
% 2.58/1.37  #SimpNegUnit  : 1
% 2.58/1.37  #BackRed      : 2
% 2.58/1.37  
% 2.58/1.37  #Partial instantiations: 0
% 2.58/1.37  #Strategies tried      : 1
% 2.58/1.37  
% 2.58/1.37  Timing (in seconds)
% 2.58/1.37  ----------------------
% 2.58/1.37  Preprocessing        : 0.32
% 2.58/1.37  Parsing              : 0.18
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.26
% 2.58/1.37  Inferencing          : 0.11
% 2.58/1.37  Reduction            : 0.07
% 2.58/1.37  Demodulation         : 0.05
% 2.58/1.37  BG Simplification    : 0.02
% 2.58/1.37  Subsumption          : 0.05
% 2.58/1.37  Abstraction          : 0.02
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.62
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
