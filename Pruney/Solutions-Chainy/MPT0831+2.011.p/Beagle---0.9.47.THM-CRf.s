%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   62 (  72 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 114 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_303,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( r2_relset_1(A_112,B_113,C_114,C_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_349,plain,(
    ! [C_128] :
      ( r2_relset_1('#skF_2','#skF_1',C_128,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_303])).

tff(c_356,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_349])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_55,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_46])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,C_3))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_zfmisc_1(A_4),k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_218,plain,(
    ! [A_88,C_89,B_90] :
      ( m1_subset_1(A_88,C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_311,plain,(
    ! [A_116,B_117,A_118] :
      ( m1_subset_1(A_116,B_117)
      | ~ r2_hidden(A_116,A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_553,plain,(
    ! [A_195,B_196,B_197] :
      ( m1_subset_1(A_195,B_196)
      | ~ r1_tarski(B_197,B_196)
      | v1_xboole_0(B_197)
      | ~ m1_subset_1(A_195,B_197) ) ),
    inference(resolution,[status(thm)],[c_10,c_311])).

tff(c_559,plain,(
    ! [A_195,B_5,A_4] :
      ( m1_subset_1(A_195,k1_zfmisc_1(B_5))
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_195,k1_zfmisc_1(A_4))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_553])).

tff(c_838,plain,(
    ! [A_292,B_293,A_294] :
      ( m1_subset_1(A_292,k1_zfmisc_1(B_293))
      | ~ m1_subset_1(A_292,k1_zfmisc_1(A_294))
      | ~ r1_tarski(A_294,B_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_559])).

tff(c_847,plain,(
    ! [B_297] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_297))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),B_297) ) ),
    inference(resolution,[status(thm)],[c_34,c_838])).

tff(c_858,plain,(
    ! [B_298] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_298,'#skF_1')))
      | ~ r1_tarski('#skF_2',B_298) ) ),
    inference(resolution,[status(thm)],[c_4,c_847])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_897,plain,(
    ! [B_299] :
      ( v4_relat_1('#skF_4',B_299)
      | ~ r1_tarski('#skF_2',B_299) ) ),
    inference(resolution,[status(thm)],[c_858,c_24])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_900,plain,(
    ! [B_299] :
      ( k7_relat_1('#skF_4',B_299) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_299) ) ),
    inference(resolution,[status(thm)],[c_897,c_18])).

tff(c_904,plain,(
    ! [B_300] :
      ( k7_relat_1('#skF_4',B_300) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_900])).

tff(c_908,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_904])).

tff(c_276,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k5_relset_1(A_106,B_107,C_108,D_109) = k7_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_283,plain,(
    ! [D_109] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_109) = k7_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_34,c_276])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_284,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_30])).

tff(c_909,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_284])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:17:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.55  
% 3.48/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.55  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.48/1.55  
% 3.48/1.55  %Foreground sorts:
% 3.48/1.55  
% 3.48/1.55  
% 3.48/1.55  %Background operators:
% 3.48/1.55  
% 3.48/1.55  
% 3.48/1.55  %Foreground operators:
% 3.48/1.55  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.48/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.55  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.48/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.48/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.48/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.48/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.48/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.55  
% 3.48/1.56  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 3.48/1.56  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.48/1.56  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.48/1.56  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.48/1.56  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.48/1.56  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.48/1.56  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.48/1.56  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.56  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.48/1.56  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.48/1.56  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.48/1.56  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.48/1.56  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.56  tff(c_303, plain, (![A_112, B_113, C_114, D_115]: (r2_relset_1(A_112, B_113, C_114, C_114) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.56  tff(c_349, plain, (![C_128]: (r2_relset_1('#skF_2', '#skF_1', C_128, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_34, c_303])).
% 3.48/1.56  tff(c_356, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_349])).
% 3.48/1.56  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.56  tff(c_46, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.48/1.56  tff(c_55, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_46])).
% 3.48/1.56  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, C_3)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.56  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.48/1.56  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_zfmisc_1(A_4), k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.56  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.48/1.56  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.48/1.56  tff(c_218, plain, (![A_88, C_89, B_90]: (m1_subset_1(A_88, C_89) | ~m1_subset_1(B_90, k1_zfmisc_1(C_89)) | ~r2_hidden(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.56  tff(c_311, plain, (![A_116, B_117, A_118]: (m1_subset_1(A_116, B_117) | ~r2_hidden(A_116, A_118) | ~r1_tarski(A_118, B_117))), inference(resolution, [status(thm)], [c_14, c_218])).
% 3.48/1.56  tff(c_553, plain, (![A_195, B_196, B_197]: (m1_subset_1(A_195, B_196) | ~r1_tarski(B_197, B_196) | v1_xboole_0(B_197) | ~m1_subset_1(A_195, B_197))), inference(resolution, [status(thm)], [c_10, c_311])).
% 3.48/1.56  tff(c_559, plain, (![A_195, B_5, A_4]: (m1_subset_1(A_195, k1_zfmisc_1(B_5)) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_195, k1_zfmisc_1(A_4)) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_553])).
% 3.48/1.56  tff(c_838, plain, (![A_292, B_293, A_294]: (m1_subset_1(A_292, k1_zfmisc_1(B_293)) | ~m1_subset_1(A_292, k1_zfmisc_1(A_294)) | ~r1_tarski(A_294, B_293))), inference(negUnitSimplification, [status(thm)], [c_8, c_559])).
% 3.48/1.56  tff(c_847, plain, (![B_297]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_297)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), B_297))), inference(resolution, [status(thm)], [c_34, c_838])).
% 3.48/1.56  tff(c_858, plain, (![B_298]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_298, '#skF_1'))) | ~r1_tarski('#skF_2', B_298))), inference(resolution, [status(thm)], [c_4, c_847])).
% 3.48/1.56  tff(c_24, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.56  tff(c_897, plain, (![B_299]: (v4_relat_1('#skF_4', B_299) | ~r1_tarski('#skF_2', B_299))), inference(resolution, [status(thm)], [c_858, c_24])).
% 3.48/1.56  tff(c_18, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.48/1.56  tff(c_900, plain, (![B_299]: (k7_relat_1('#skF_4', B_299)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_299))), inference(resolution, [status(thm)], [c_897, c_18])).
% 3.48/1.56  tff(c_904, plain, (![B_300]: (k7_relat_1('#skF_4', B_300)='#skF_4' | ~r1_tarski('#skF_2', B_300))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_900])).
% 3.48/1.56  tff(c_908, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_904])).
% 3.48/1.56  tff(c_276, plain, (![A_106, B_107, C_108, D_109]: (k5_relset_1(A_106, B_107, C_108, D_109)=k7_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.56  tff(c_283, plain, (![D_109]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_109)=k7_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_34, c_276])).
% 3.48/1.56  tff(c_30, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.56  tff(c_284, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_30])).
% 3.48/1.56  tff(c_909, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_284])).
% 3.48/1.56  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_909])).
% 3.48/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.56  
% 3.48/1.56  Inference rules
% 3.48/1.56  ----------------------
% 3.48/1.56  #Ref     : 0
% 3.48/1.56  #Sup     : 219
% 3.48/1.56  #Fact    : 0
% 3.48/1.56  #Define  : 0
% 3.48/1.56  #Split   : 2
% 3.48/1.56  #Chain   : 0
% 3.48/1.56  #Close   : 0
% 3.48/1.56  
% 3.48/1.56  Ordering : KBO
% 3.48/1.56  
% 3.48/1.56  Simplification rules
% 3.48/1.56  ----------------------
% 3.48/1.56  #Subsume      : 1
% 3.48/1.56  #Demod        : 24
% 3.48/1.56  #Tautology    : 24
% 3.48/1.56  #SimpNegUnit  : 1
% 3.48/1.56  #BackRed      : 2
% 3.48/1.56  
% 3.48/1.56  #Partial instantiations: 0
% 3.48/1.56  #Strategies tried      : 1
% 3.48/1.56  
% 3.48/1.56  Timing (in seconds)
% 3.48/1.56  ----------------------
% 3.48/1.57  Preprocessing        : 0.31
% 3.48/1.57  Parsing              : 0.17
% 3.48/1.57  CNF conversion       : 0.02
% 3.48/1.57  Main loop            : 0.50
% 3.48/1.57  Inferencing          : 0.19
% 3.48/1.57  Reduction            : 0.15
% 3.48/1.57  Demodulation         : 0.10
% 3.48/1.57  BG Simplification    : 0.02
% 3.48/1.57  Subsumption          : 0.10
% 3.48/1.57  Abstraction          : 0.02
% 3.48/1.57  MUC search           : 0.00
% 3.48/1.57  Cooper               : 0.00
% 3.48/1.57  Total                : 0.84
% 3.48/1.57  Index Insertion      : 0.00
% 3.48/1.57  Index Deletion       : 0.00
% 3.48/1.57  Index Matching       : 0.00
% 3.48/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
