%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 138 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 232 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_39,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_29,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_116,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_52,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_37,c_116])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_4,A_35,B_36] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_35,B_36)) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_155,plain,(
    ! [A_53] :
      ( v1_relat_1(A_53)
      | ~ r1_tarski(A_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_47])).

tff(c_166,plain,(
    ! [A_10] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_10))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_172,plain,(
    ! [A_10] : v1_relat_1(k7_relat_1('#skF_4',A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_166])).

tff(c_69,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [A_4,A_41,B_42] :
      ( v4_relat_1(A_4,A_41)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_177,plain,(
    ! [A_55] :
      ( v4_relat_1(A_55,'#skF_1')
      | ~ r1_tarski(A_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_77])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,'#skF_1') = A_69
      | ~ v1_relat_1(A_69)
      | ~ r1_tarski(A_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_177,c_8])).

tff(c_248,plain,(
    ! [A_10] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_10),'#skF_1') = k7_relat_1('#skF_4',A_10)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_10))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_237])).

tff(c_256,plain,(
    ! [A_70] : k7_relat_1(k7_relat_1('#skF_4',A_70),'#skF_1') = k7_relat_1('#skF_4',A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_172,c_248])).

tff(c_265,plain,(
    ! [A_70] :
      ( r1_tarski(k7_relat_1('#skF_4',A_70),k7_relat_1('#skF_4',A_70))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_12])).

tff(c_276,plain,(
    ! [A_70] : r1_tarski(k7_relat_1('#skF_4',A_70),k7_relat_1('#skF_4',A_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_265])).

tff(c_357,plain,(
    ! [A_85,B_86,A_87] :
      ( r1_tarski(A_85,B_86)
      | ~ r1_tarski(A_85,k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_360,plain,(
    ! [A_70] :
      ( r1_tarski(k7_relat_1('#skF_4',A_70),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_276,c_357])).

tff(c_377,plain,(
    ! [A_70] : r1_tarski(k7_relat_1('#skF_4',A_70),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_360])).

tff(c_124,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_37,c_116])).

tff(c_349,plain,(
    ! [D_81,B_82,C_83,A_84] :
      ( m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(B_82,C_83)))
      | ~ r1_tarski(k1_relat_1(D_81),B_82)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_84,C_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_738,plain,(
    ! [A_140,B_141,C_142,A_143] :
      ( m1_subset_1(A_140,k1_zfmisc_1(k2_zfmisc_1(B_141,C_142)))
      | ~ r1_tarski(k1_relat_1(A_140),B_141)
      | ~ r1_tarski(A_140,k2_zfmisc_1(A_143,C_142)) ) ),
    inference(resolution,[status(thm)],[c_6,c_349])).

tff(c_792,plain,(
    ! [A_152,B_153] :
      ( m1_subset_1(A_152,k1_zfmisc_1(k2_zfmisc_1(B_153,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(A_152),B_153)
      | ~ r1_tarski(A_152,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_124,c_738])).

tff(c_304,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k5_relset_1(A_73,B_74,C_75,D_76) = k7_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_311,plain,(
    ! [D_76] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_76) = k7_relat_1('#skF_4',D_76) ),
    inference(resolution,[status(thm)],[c_26,c_304])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_313,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_24])).

tff(c_797,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_792,c_313])).

tff(c_815,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_797])).

tff(c_823,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_815])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.36  
% 2.71/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.36  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.36  
% 2.71/1.36  %Foreground sorts:
% 2.71/1.36  
% 2.71/1.36  
% 2.71/1.36  %Background operators:
% 2.71/1.36  
% 2.71/1.36  
% 2.71/1.36  %Foreground operators:
% 2.71/1.36  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.71/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.71/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.71/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.36  
% 2.71/1.38  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.71/1.38  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.71/1.38  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.71/1.38  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.71/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.71/1.38  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.71/1.38  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.71/1.38  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.71/1.38  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.71/1.38  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.71/1.38  tff(c_39, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.38  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_39])).
% 2.71/1.38  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.38  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.71/1.38  tff(c_29, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.38  tff(c_37, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.71/1.38  tff(c_116, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.38  tff(c_143, plain, (![A_52]: (r1_tarski(A_52, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_52, '#skF_4'))), inference(resolution, [status(thm)], [c_37, c_116])).
% 2.71/1.38  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.38  tff(c_47, plain, (![A_4, A_35, B_36]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_35, B_36)))), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.71/1.38  tff(c_155, plain, (![A_53]: (v1_relat_1(A_53) | ~r1_tarski(A_53, '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_47])).
% 2.71/1.38  tff(c_166, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_4', A_10)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_155])).
% 2.71/1.38  tff(c_172, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_4', A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_166])).
% 2.71/1.38  tff(c_69, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.71/1.38  tff(c_77, plain, (![A_4, A_41, B_42]: (v4_relat_1(A_4, A_41) | ~r1_tarski(A_4, k2_zfmisc_1(A_41, B_42)))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.71/1.38  tff(c_177, plain, (![A_55]: (v4_relat_1(A_55, '#skF_1') | ~r1_tarski(A_55, '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_77])).
% 2.71/1.38  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.38  tff(c_237, plain, (![A_69]: (k7_relat_1(A_69, '#skF_1')=A_69 | ~v1_relat_1(A_69) | ~r1_tarski(A_69, '#skF_4'))), inference(resolution, [status(thm)], [c_177, c_8])).
% 2.71/1.38  tff(c_248, plain, (![A_10]: (k7_relat_1(k7_relat_1('#skF_4', A_10), '#skF_1')=k7_relat_1('#skF_4', A_10) | ~v1_relat_1(k7_relat_1('#skF_4', A_10)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_237])).
% 2.71/1.38  tff(c_256, plain, (![A_70]: (k7_relat_1(k7_relat_1('#skF_4', A_70), '#skF_1')=k7_relat_1('#skF_4', A_70))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_172, c_248])).
% 2.71/1.38  tff(c_265, plain, (![A_70]: (r1_tarski(k7_relat_1('#skF_4', A_70), k7_relat_1('#skF_4', A_70)) | ~v1_relat_1(k7_relat_1('#skF_4', A_70)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_12])).
% 2.71/1.38  tff(c_276, plain, (![A_70]: (r1_tarski(k7_relat_1('#skF_4', A_70), k7_relat_1('#skF_4', A_70)))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_265])).
% 2.71/1.38  tff(c_357, plain, (![A_85, B_86, A_87]: (r1_tarski(A_85, B_86) | ~r1_tarski(A_85, k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_12, c_116])).
% 2.71/1.38  tff(c_360, plain, (![A_70]: (r1_tarski(k7_relat_1('#skF_4', A_70), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_276, c_357])).
% 2.71/1.38  tff(c_377, plain, (![A_70]: (r1_tarski(k7_relat_1('#skF_4', A_70), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_360])).
% 2.71/1.38  tff(c_124, plain, (![A_48]: (r1_tarski(A_48, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_37, c_116])).
% 2.71/1.38  tff(c_349, plain, (![D_81, B_82, C_83, A_84]: (m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(B_82, C_83))) | ~r1_tarski(k1_relat_1(D_81), B_82) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_84, C_83))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.38  tff(c_738, plain, (![A_140, B_141, C_142, A_143]: (m1_subset_1(A_140, k1_zfmisc_1(k2_zfmisc_1(B_141, C_142))) | ~r1_tarski(k1_relat_1(A_140), B_141) | ~r1_tarski(A_140, k2_zfmisc_1(A_143, C_142)))), inference(resolution, [status(thm)], [c_6, c_349])).
% 2.71/1.38  tff(c_792, plain, (![A_152, B_153]: (m1_subset_1(A_152, k1_zfmisc_1(k2_zfmisc_1(B_153, '#skF_3'))) | ~r1_tarski(k1_relat_1(A_152), B_153) | ~r1_tarski(A_152, '#skF_4'))), inference(resolution, [status(thm)], [c_124, c_738])).
% 2.71/1.38  tff(c_304, plain, (![A_73, B_74, C_75, D_76]: (k5_relset_1(A_73, B_74, C_75, D_76)=k7_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.38  tff(c_311, plain, (![D_76]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_76)=k7_relat_1('#skF_4', D_76))), inference(resolution, [status(thm)], [c_26, c_304])).
% 2.71/1.38  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.71/1.38  tff(c_313, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_24])).
% 2.71/1.38  tff(c_797, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_792, c_313])).
% 2.71/1.38  tff(c_815, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_797])).
% 2.71/1.38  tff(c_823, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_815])).
% 2.71/1.38  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_823])).
% 2.71/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  
% 2.71/1.38  Inference rules
% 2.71/1.38  ----------------------
% 2.71/1.38  #Ref     : 0
% 2.71/1.38  #Sup     : 182
% 2.71/1.38  #Fact    : 0
% 2.71/1.38  #Define  : 0
% 2.71/1.38  #Split   : 3
% 2.71/1.38  #Chain   : 0
% 2.71/1.38  #Close   : 0
% 2.71/1.38  
% 2.71/1.38  Ordering : KBO
% 2.71/1.38  
% 2.71/1.38  Simplification rules
% 2.71/1.38  ----------------------
% 2.71/1.38  #Subsume      : 18
% 2.71/1.38  #Demod        : 80
% 2.71/1.38  #Tautology    : 59
% 2.71/1.38  #SimpNegUnit  : 0
% 2.71/1.38  #BackRed      : 2
% 2.71/1.38  
% 2.71/1.38  #Partial instantiations: 0
% 2.71/1.38  #Strategies tried      : 1
% 2.71/1.38  
% 2.71/1.38  Timing (in seconds)
% 2.71/1.38  ----------------------
% 2.98/1.38  Preprocessing        : 0.28
% 2.98/1.38  Parsing              : 0.15
% 2.98/1.38  CNF conversion       : 0.02
% 2.98/1.38  Main loop            : 0.38
% 2.98/1.38  Inferencing          : 0.15
% 2.98/1.38  Reduction            : 0.11
% 2.98/1.38  Demodulation         : 0.08
% 2.98/1.38  BG Simplification    : 0.02
% 2.98/1.38  Subsumption          : 0.08
% 2.98/1.38  Abstraction          : 0.02
% 2.98/1.38  MUC search           : 0.00
% 2.98/1.38  Cooper               : 0.00
% 2.98/1.38  Total                : 0.70
% 2.98/1.38  Index Insertion      : 0.00
% 2.98/1.38  Index Deletion       : 0.00
% 2.98/1.38  Index Matching       : 0.00
% 2.98/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
