%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 296 expanded)
%              Number of leaves         :   37 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  125 ( 678 expanded)
%              Number of equality atoms :   20 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_93,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_167,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_176,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_167])).

tff(c_42,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_177,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_42])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_135,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,A_62) = B_61
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_135])).

tff(c_141,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_138])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_145,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_24])).

tff(c_149,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_145])).

tff(c_218,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden(k4_tarski('#skF_1'(A_99,B_100,C_101),A_99),C_101)
      | ~ r2_hidden(A_99,k9_relat_1(C_101,B_100))
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_244,plain,(
    ! [C_107,A_108,B_109] :
      ( k1_funct_1(C_107,'#skF_1'(A_108,B_109,C_107)) = A_108
      | ~ v1_funct_1(C_107)
      | ~ r2_hidden(A_108,k9_relat_1(C_107,B_109))
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_218,c_30])).

tff(c_255,plain,(
    ! [A_108] :
      ( k1_funct_1('#skF_5','#skF_1'(A_108,'#skF_3','#skF_5')) = A_108
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_108,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_244])).

tff(c_277,plain,(
    ! [A_114] :
      ( k1_funct_1('#skF_5','#skF_1'(A_114,'#skF_3','#skF_5')) = A_114
      | ~ r2_hidden(A_114,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48,c_255])).

tff(c_296,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_177,c_277])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_23,C_25] :
      ( r2_hidden(k4_tarski(A_23,k1_funct_1(C_25,A_23)),C_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_300,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_28])).

tff(c_304,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48,c_300])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_329,plain,
    ( ~ r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_306])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_177,c_149,c_329])).

tff(c_335,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [A_65,B_2,A_1] :
      ( m1_subset_1(A_65,B_2)
      | ~ r2_hidden(A_65,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_360,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),B_117)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_117) ) ),
    inference(resolution,[status(thm)],[c_335,c_165])).

tff(c_364,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),A_9)
      | ~ v4_relat_1('#skF_5',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_360])).

tff(c_368,plain,(
    ! [A_118] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),A_118)
      | ~ v4_relat_1('#skF_5',A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_364])).

tff(c_40,plain,(
    ! [E_33] :
      ( k1_funct_1('#skF_5',E_33) != '#skF_2'
      | ~ m1_subset_1(E_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_395,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2'
    | ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_368,c_40])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_296,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.47/1.36  
% 2.47/1.36  %Foreground sorts:
% 2.47/1.36  
% 2.47/1.36  
% 2.47/1.36  %Background operators:
% 2.47/1.36  
% 2.47/1.36  
% 2.47/1.36  %Foreground operators:
% 2.47/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.47/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.47/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.47/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.47/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.47/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.36  
% 2.77/1.38  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.77/1.38  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.38  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.77/1.38  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.38  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.38  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.77/1.38  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.77/1.38  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.77/1.38  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.77/1.38  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.77/1.38  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.38  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.77/1.38  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.38  tff(c_84, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.77/1.38  tff(c_93, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_84])).
% 2.77/1.38  tff(c_167, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.77/1.38  tff(c_176, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_167])).
% 2.77/1.38  tff(c_42, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.38  tff(c_177, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_42])).
% 2.77/1.38  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.77/1.38  tff(c_61, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.38  tff(c_67, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_61])).
% 2.77/1.38  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_67])).
% 2.77/1.38  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.38  tff(c_135, plain, (![B_61, A_62]: (k7_relat_1(B_61, A_62)=B_61 | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.77/1.38  tff(c_138, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_93, c_135])).
% 2.77/1.38  tff(c_141, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_138])).
% 2.77/1.38  tff(c_24, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.38  tff(c_145, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_141, c_24])).
% 2.77/1.38  tff(c_149, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_145])).
% 2.77/1.38  tff(c_218, plain, (![A_99, B_100, C_101]: (r2_hidden(k4_tarski('#skF_1'(A_99, B_100, C_101), A_99), C_101) | ~r2_hidden(A_99, k9_relat_1(C_101, B_100)) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.38  tff(c_30, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.77/1.38  tff(c_244, plain, (![C_107, A_108, B_109]: (k1_funct_1(C_107, '#skF_1'(A_108, B_109, C_107))=A_108 | ~v1_funct_1(C_107) | ~r2_hidden(A_108, k9_relat_1(C_107, B_109)) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_218, c_30])).
% 2.77/1.38  tff(c_255, plain, (![A_108]: (k1_funct_1('#skF_5', '#skF_1'(A_108, '#skF_3', '#skF_5'))=A_108 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_108, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_244])).
% 2.77/1.38  tff(c_277, plain, (![A_114]: (k1_funct_1('#skF_5', '#skF_1'(A_114, '#skF_3', '#skF_5'))=A_114 | ~r2_hidden(A_114, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48, c_255])).
% 2.77/1.38  tff(c_296, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_177, c_277])).
% 2.77/1.38  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.38  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.38  tff(c_28, plain, (![A_23, C_25]: (r2_hidden(k4_tarski(A_23, k1_funct_1(C_25, A_23)), C_25) | ~r2_hidden(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.77/1.38  tff(c_300, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_296, c_28])).
% 2.77/1.38  tff(c_304, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48, c_300])).
% 2.77/1.38  tff(c_306, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.77/1.38  tff(c_329, plain, (~r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_306])).
% 2.77/1.38  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_177, c_149, c_329])).
% 2.77/1.38  tff(c_335, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_304])).
% 2.77/1.38  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.38  tff(c_160, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.38  tff(c_165, plain, (![A_65, B_2, A_1]: (m1_subset_1(A_65, B_2) | ~r2_hidden(A_65, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_160])).
% 2.77/1.38  tff(c_360, plain, (![B_117]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), B_117) | ~r1_tarski(k1_relat_1('#skF_5'), B_117))), inference(resolution, [status(thm)], [c_335, c_165])).
% 2.77/1.38  tff(c_364, plain, (![A_9]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), A_9) | ~v4_relat_1('#skF_5', A_9) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_360])).
% 2.77/1.38  tff(c_368, plain, (![A_118]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), A_118) | ~v4_relat_1('#skF_5', A_118))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_364])).
% 2.77/1.38  tff(c_40, plain, (![E_33]: (k1_funct_1('#skF_5', E_33)!='#skF_2' | ~m1_subset_1(E_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.38  tff(c_395, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2' | ~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_368, c_40])).
% 2.77/1.38  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_296, c_395])).
% 2.77/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  Inference rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Ref     : 0
% 2.77/1.38  #Sup     : 77
% 2.77/1.38  #Fact    : 0
% 2.77/1.38  #Define  : 0
% 2.77/1.38  #Split   : 2
% 2.77/1.38  #Chain   : 0
% 2.77/1.38  #Close   : 0
% 2.77/1.38  
% 2.77/1.38  Ordering : KBO
% 2.77/1.38  
% 2.77/1.38  Simplification rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Subsume      : 1
% 2.77/1.38  #Demod        : 26
% 2.77/1.38  #Tautology    : 20
% 2.77/1.38  #SimpNegUnit  : 0
% 2.77/1.38  #BackRed      : 1
% 2.77/1.38  
% 2.77/1.38  #Partial instantiations: 0
% 2.77/1.38  #Strategies tried      : 1
% 2.77/1.38  
% 2.77/1.38  Timing (in seconds)
% 2.77/1.38  ----------------------
% 2.77/1.38  Preprocessing        : 0.33
% 2.77/1.38  Parsing              : 0.17
% 2.77/1.38  CNF conversion       : 0.02
% 2.77/1.38  Main loop            : 0.27
% 2.77/1.38  Inferencing          : 0.10
% 2.77/1.38  Reduction            : 0.08
% 2.77/1.38  Demodulation         : 0.06
% 2.77/1.38  BG Simplification    : 0.02
% 2.77/1.38  Subsumption          : 0.05
% 2.77/1.38  Abstraction          : 0.02
% 2.77/1.38  MUC search           : 0.00
% 2.77/1.38  Cooper               : 0.00
% 2.77/1.38  Total                : 0.64
% 2.77/1.38  Index Insertion      : 0.00
% 2.77/1.38  Index Deletion       : 0.00
% 2.77/1.38  Index Matching       : 0.00
% 2.77/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
