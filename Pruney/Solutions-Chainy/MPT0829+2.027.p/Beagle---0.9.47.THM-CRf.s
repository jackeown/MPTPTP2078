%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:25 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 179 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_63,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_414,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_418,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_414])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_626,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_relset_1(A_126,B_127,C_128) = k2_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_630,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_626])).

tff(c_36,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_384,plain,(
    ! [C_82,A_83,B_84,D_85] :
      ( r1_tarski(C_82,k1_relset_1(A_83,B_84,D_85))
      | ~ r1_tarski(k6_relat_1(C_82),D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_404,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2',k1_relset_1(A_88,B_89,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(resolution,[status(thm)],[c_38,c_384])).

tff(c_407,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_404])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_407])).

tff(c_412,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_631,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_412])).

tff(c_798,plain,(
    ! [C_148,A_149,B_150,D_151] :
      ( r1_tarski(C_148,k2_relset_1(A_149,B_150,D_151))
      | ~ r1_tarski(k6_relat_1(C_148),D_151)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_806,plain,(
    ! [A_152,B_153] :
      ( r1_tarski('#skF_2',k2_relset_1(A_152,B_153,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(resolution,[status(thm)],[c_38,c_798])).

tff(c_809,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_806])).

tff(c_811,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_809])).

tff(c_14,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_17] : v4_relat_1(k6_relat_1(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_495,plain,(
    ! [C_109,B_110,A_111] :
      ( v4_relat_1(C_109,B_110)
      | ~ v4_relat_1(C_109,A_111)
      | ~ v1_relat_1(C_109)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_499,plain,(
    ! [A_17,B_110] :
      ( v4_relat_1(k6_relat_1(A_17),B_110)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ r1_tarski(A_17,B_110) ) ),
    inference(resolution,[status(thm)],[c_22,c_495])).

tff(c_534,plain,(
    ! [A_115,B_116] :
      ( v4_relat_1(k6_relat_1(A_115),B_116)
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_499])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_539,plain,(
    ! [A_115,B_116] :
      ( k7_relat_1(k6_relat_1(A_115),B_116) = k6_relat_1(A_115)
      | ~ v1_relat_1(k6_relat_1(A_115))
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_534,c_10])).

tff(c_584,plain,(
    ! [A_122,B_123] :
      ( k7_relat_1(k6_relat_1(A_122),B_123) = k6_relat_1(A_122)
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_539])).

tff(c_506,plain,(
    ! [B_112,A_113] :
      ( k1_relat_1(k7_relat_1(B_112,A_113)) = A_113
      | ~ r1_tarski(A_113,k1_relat_1(B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_517,plain,(
    ! [A_14,A_113] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_113)) = A_113
      | ~ r1_tarski(A_113,A_14)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_506])).

tff(c_521,plain,(
    ! [A_14,A_113] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_113)) = A_113
      | ~ r1_tarski(A_113,A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_517])).

tff(c_590,plain,(
    ! [A_122,B_123] :
      ( k1_relat_1(k6_relat_1(A_122)) = B_123
      | ~ r1_tarski(B_123,A_122)
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_521])).

tff(c_602,plain,(
    ! [B_123,A_122] :
      ( B_123 = A_122
      | ~ r1_tarski(B_123,A_122)
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_590])).

tff(c_815,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_811,c_602])).

tff(c_821,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_815])).

tff(c_825,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_821])).

tff(c_829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_418,c_825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.73/1.45  
% 2.73/1.45  %Foreground sorts:
% 2.73/1.45  
% 2.73/1.45  
% 2.73/1.45  %Background operators:
% 2.73/1.45  
% 2.73/1.45  
% 2.73/1.45  %Foreground operators:
% 2.73/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.73/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.73/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.45  
% 2.82/1.47  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.82/1.47  tff(f_98, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 2.82/1.47  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.82/1.47  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.47  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.82/1.47  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.82/1.47  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.82/1.47  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.82/1.47  tff(f_71, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.82/1.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.82/1.47  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.82/1.47  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.82/1.47  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.47  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.82/1.47  tff(c_63, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.47  tff(c_66, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_63])).
% 2.82/1.47  tff(c_69, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_66])).
% 2.82/1.47  tff(c_414, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.82/1.47  tff(c_418, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_414])).
% 2.82/1.47  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.47  tff(c_626, plain, (![A_126, B_127, C_128]: (k2_relset_1(A_126, B_127, C_128)=k2_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.82/1.47  tff(c_630, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_626])).
% 2.82/1.47  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.82/1.47  tff(c_70, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.82/1.47  tff(c_38, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.82/1.47  tff(c_384, plain, (![C_82, A_83, B_84, D_85]: (r1_tarski(C_82, k1_relset_1(A_83, B_84, D_85)) | ~r1_tarski(k6_relat_1(C_82), D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.82/1.47  tff(c_404, plain, (![A_88, B_89]: (r1_tarski('#skF_2', k1_relset_1(A_88, B_89, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(resolution, [status(thm)], [c_38, c_384])).
% 2.82/1.47  tff(c_407, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_404])).
% 2.82/1.47  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_407])).
% 2.82/1.47  tff(c_412, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.82/1.47  tff(c_631, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_630, c_412])).
% 2.82/1.47  tff(c_798, plain, (![C_148, A_149, B_150, D_151]: (r1_tarski(C_148, k2_relset_1(A_149, B_150, D_151)) | ~r1_tarski(k6_relat_1(C_148), D_151) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.82/1.47  tff(c_806, plain, (![A_152, B_153]: (r1_tarski('#skF_2', k2_relset_1(A_152, B_153, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(resolution, [status(thm)], [c_38, c_798])).
% 2.82/1.47  tff(c_809, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_806])).
% 2.82/1.47  tff(c_811, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_809])).
% 2.82/1.47  tff(c_14, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.47  tff(c_20, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.47  tff(c_22, plain, (![A_17]: (v4_relat_1(k6_relat_1(A_17), A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.47  tff(c_495, plain, (![C_109, B_110, A_111]: (v4_relat_1(C_109, B_110) | ~v4_relat_1(C_109, A_111) | ~v1_relat_1(C_109) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.47  tff(c_499, plain, (![A_17, B_110]: (v4_relat_1(k6_relat_1(A_17), B_110) | ~v1_relat_1(k6_relat_1(A_17)) | ~r1_tarski(A_17, B_110))), inference(resolution, [status(thm)], [c_22, c_495])).
% 2.82/1.47  tff(c_534, plain, (![A_115, B_116]: (v4_relat_1(k6_relat_1(A_115), B_116) | ~r1_tarski(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_499])).
% 2.82/1.47  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.82/1.47  tff(c_539, plain, (![A_115, B_116]: (k7_relat_1(k6_relat_1(A_115), B_116)=k6_relat_1(A_115) | ~v1_relat_1(k6_relat_1(A_115)) | ~r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_534, c_10])).
% 2.82/1.47  tff(c_584, plain, (![A_122, B_123]: (k7_relat_1(k6_relat_1(A_122), B_123)=k6_relat_1(A_122) | ~r1_tarski(A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_539])).
% 2.82/1.47  tff(c_506, plain, (![B_112, A_113]: (k1_relat_1(k7_relat_1(B_112, A_113))=A_113 | ~r1_tarski(A_113, k1_relat_1(B_112)) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.47  tff(c_517, plain, (![A_14, A_113]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_113))=A_113 | ~r1_tarski(A_113, A_14) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_506])).
% 2.82/1.47  tff(c_521, plain, (![A_14, A_113]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_113))=A_113 | ~r1_tarski(A_113, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_517])).
% 2.82/1.47  tff(c_590, plain, (![A_122, B_123]: (k1_relat_1(k6_relat_1(A_122))=B_123 | ~r1_tarski(B_123, A_122) | ~r1_tarski(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_584, c_521])).
% 2.82/1.47  tff(c_602, plain, (![B_123, A_122]: (B_123=A_122 | ~r1_tarski(B_123, A_122) | ~r1_tarski(A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_590])).
% 2.82/1.47  tff(c_815, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_811, c_602])).
% 2.82/1.47  tff(c_821, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_631, c_815])).
% 2.82/1.47  tff(c_825, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_821])).
% 2.82/1.47  tff(c_829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_418, c_825])).
% 2.82/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.47  
% 2.82/1.47  Inference rules
% 2.82/1.47  ----------------------
% 2.82/1.47  #Ref     : 0
% 2.82/1.47  #Sup     : 163
% 2.82/1.47  #Fact    : 0
% 2.82/1.47  #Define  : 0
% 2.82/1.47  #Split   : 7
% 2.82/1.47  #Chain   : 0
% 2.82/1.47  #Close   : 0
% 2.82/1.47  
% 2.82/1.47  Ordering : KBO
% 2.82/1.47  
% 2.82/1.47  Simplification rules
% 2.82/1.47  ----------------------
% 2.82/1.47  #Subsume      : 10
% 2.82/1.47  #Demod        : 109
% 2.82/1.47  #Tautology    : 63
% 2.82/1.47  #SimpNegUnit  : 2
% 2.82/1.47  #BackRed      : 1
% 2.82/1.47  
% 2.82/1.47  #Partial instantiations: 0
% 2.82/1.47  #Strategies tried      : 1
% 2.82/1.47  
% 2.82/1.47  Timing (in seconds)
% 2.82/1.47  ----------------------
% 2.82/1.47  Preprocessing        : 0.28
% 2.82/1.47  Parsing              : 0.15
% 2.82/1.47  CNF conversion       : 0.02
% 2.82/1.47  Main loop            : 0.34
% 2.82/1.47  Inferencing          : 0.13
% 2.82/1.47  Reduction            : 0.11
% 2.82/1.47  Demodulation         : 0.08
% 2.82/1.47  BG Simplification    : 0.02
% 2.82/1.47  Subsumption          : 0.06
% 2.82/1.47  Abstraction          : 0.02
% 2.82/1.47  MUC search           : 0.00
% 2.82/1.47  Cooper               : 0.00
% 2.82/1.47  Total                : 0.65
% 2.82/1.47  Index Insertion      : 0.00
% 2.82/1.47  Index Deletion       : 0.00
% 2.82/1.47  Index Matching       : 0.00
% 2.82/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
