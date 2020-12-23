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
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 261 expanded)
%              Number of leaves         :   44 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 514 expanded)
%              Number of equality atoms :   46 ( 130 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_92,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,A_13),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_96,c_28])).

tff(c_110,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_97,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_101,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_150,plain,(
    ! [B_63,A_64] :
      ( k7_relat_1(B_63,A_64) = B_63
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_101,c_150])).

tff(c_156,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_153])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_160,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_18])).

tff(c_164,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_160])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k9_relat_1(A_10,k1_tarski(B_12)) = k11_relat_1(A_10,B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_169,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_14])).

tff(c_179,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_169])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,k1_relat_1(B_19))
      | k11_relat_1(B_19,A_18) = k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ! [B_74,A_75] :
      ( k1_relat_1(k7_relat_1(B_74,A_75)) = A_75
      | ~ r1_tarski(A_75,k1_relat_1(B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_243,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(k7_relat_1(B_77,k1_tarski(A_78))) = k1_tarski(A_78)
      | ~ v1_relat_1(B_77)
      | ~ r2_hidden(A_78,k1_relat_1(B_77)) ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_261,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_243])).

tff(c_265,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_261])).

tff(c_266,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_269,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_266])).

tff(c_272,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_179,c_269])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_272])).

tff(c_275,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(k1_funct_1(B_26,A_25)) = k2_relat_1(B_26)
      | k1_tarski(A_25) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_281,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_48])).

tff(c_42,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k7_relset_1(A_33,B_34,C_35,D_36) = k9_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_324,plain,(
    ! [D_36] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_36) = k9_relat_1('#skF_4',D_36) ),
    inference(resolution,[status(thm)],[c_281,c_42])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_280,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_44])).

tff(c_422,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_280])).

tff(c_425,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_422])).

tff(c_427,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_52,c_275,c_425])).

tff(c_430,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_427])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_430])).

tff(c_435,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_440,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_2])).

tff(c_20,plain,(
    ! [A_17] : k9_relat_1(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_439,plain,(
    ! [A_17] : k9_relat_1('#skF_4',A_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_435,c_20])).

tff(c_667,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_669,plain,(
    ! [D_122] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_122) = k9_relat_1('#skF_4',D_122) ),
    inference(resolution,[status(thm)],[c_48,c_667])).

tff(c_671,plain,(
    ! [D_122] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_122) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_669])).

tff(c_672,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_44])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.94  
% 3.49/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.49/1.94  
% 3.49/1.94  %Foreground sorts:
% 3.49/1.94  
% 3.49/1.94  
% 3.49/1.94  %Background operators:
% 3.49/1.94  
% 3.49/1.94  
% 3.49/1.94  %Foreground operators:
% 3.49/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.49/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.49/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.94  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.49/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.94  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.49/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.94  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.94  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.94  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.94  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.94  
% 3.49/1.97  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.49/1.97  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.97  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.49/1.97  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.49/1.97  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.97  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.49/1.97  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.49/1.97  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.49/1.97  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.49/1.97  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.49/1.97  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.49/1.97  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.49/1.97  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.49/1.97  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.49/1.97  tff(f_52, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.49/1.97  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.49/1.97  tff(c_92, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.49/1.97  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_92])).
% 3.49/1.97  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, A_13), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.49/1.97  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.49/1.97  tff(c_28, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.97  tff(c_108, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_96, c_28])).
% 3.49/1.97  tff(c_110, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_108])).
% 3.49/1.97  tff(c_97, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.49/1.97  tff(c_101, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_97])).
% 3.49/1.97  tff(c_150, plain, (![B_63, A_64]: (k7_relat_1(B_63, A_64)=B_63 | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.49/1.97  tff(c_153, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_101, c_150])).
% 3.49/1.97  tff(c_156, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_153])).
% 3.49/1.97  tff(c_18, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.49/1.97  tff(c_160, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_156, c_18])).
% 3.49/1.97  tff(c_164, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_160])).
% 3.49/1.97  tff(c_14, plain, (![A_10, B_12]: (k9_relat_1(A_10, k1_tarski(B_12))=k11_relat_1(A_10, B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.49/1.97  tff(c_169, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_164, c_14])).
% 3.49/1.97  tff(c_179, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_169])).
% 3.49/1.97  tff(c_22, plain, (![A_18, B_19]: (r2_hidden(A_18, k1_relat_1(B_19)) | k11_relat_1(B_19, A_18)=k1_xboole_0 | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.49/1.97  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.49/1.97  tff(c_214, plain, (![B_74, A_75]: (k1_relat_1(k7_relat_1(B_74, A_75))=A_75 | ~r1_tarski(A_75, k1_relat_1(B_74)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.97  tff(c_243, plain, (![B_77, A_78]: (k1_relat_1(k7_relat_1(B_77, k1_tarski(A_78)))=k1_tarski(A_78) | ~v1_relat_1(B_77) | ~r2_hidden(A_78, k1_relat_1(B_77)))), inference(resolution, [status(thm)], [c_12, c_214])).
% 3.49/1.97  tff(c_261, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_243])).
% 3.49/1.97  tff(c_265, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_261])).
% 3.49/1.97  tff(c_266, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_265])).
% 3.49/1.97  tff(c_269, plain, (k11_relat_1('#skF_4', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_266])).
% 3.49/1.97  tff(c_272, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96, c_179, c_269])).
% 3.49/1.97  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_272])).
% 3.49/1.97  tff(c_275, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_265])).
% 3.49/1.97  tff(c_34, plain, (![B_26, A_25]: (k1_tarski(k1_funct_1(B_26, A_25))=k2_relat_1(B_26) | k1_tarski(A_25)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.49/1.97  tff(c_281, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_48])).
% 3.49/1.97  tff(c_42, plain, (![A_33, B_34, C_35, D_36]: (k7_relset_1(A_33, B_34, C_35, D_36)=k9_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.97  tff(c_324, plain, (![D_36]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_36)=k9_relat_1('#skF_4', D_36))), inference(resolution, [status(thm)], [c_281, c_42])).
% 3.49/1.97  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.49/1.97  tff(c_280, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_44])).
% 3.49/1.97  tff(c_422, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_280])).
% 3.49/1.97  tff(c_425, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_422])).
% 3.49/1.97  tff(c_427, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_52, c_275, c_425])).
% 3.49/1.97  tff(c_430, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_427])).
% 3.49/1.97  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_430])).
% 3.49/1.97  tff(c_435, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_108])).
% 3.49/1.97  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.97  tff(c_440, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_2])).
% 3.49/1.97  tff(c_20, plain, (![A_17]: (k9_relat_1(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.97  tff(c_439, plain, (![A_17]: (k9_relat_1('#skF_4', A_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_435, c_20])).
% 3.49/1.97  tff(c_667, plain, (![A_119, B_120, C_121, D_122]: (k7_relset_1(A_119, B_120, C_121, D_122)=k9_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.97  tff(c_669, plain, (![D_122]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_122)=k9_relat_1('#skF_4', D_122))), inference(resolution, [status(thm)], [c_48, c_667])).
% 3.49/1.97  tff(c_671, plain, (![D_122]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_122)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_439, c_669])).
% 3.49/1.97  tff(c_672, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_671, c_44])).
% 3.49/1.97  tff(c_675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_440, c_672])).
% 3.49/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.97  
% 3.49/1.97  Inference rules
% 3.49/1.97  ----------------------
% 3.49/1.97  #Ref     : 0
% 3.49/1.97  #Sup     : 141
% 3.49/1.97  #Fact    : 0
% 3.49/1.97  #Define  : 0
% 3.49/1.97  #Split   : 6
% 3.49/1.97  #Chain   : 0
% 3.49/1.97  #Close   : 0
% 3.49/1.97  
% 3.49/1.97  Ordering : KBO
% 3.49/1.97  
% 3.49/1.97  Simplification rules
% 3.49/1.97  ----------------------
% 3.49/1.97  #Subsume      : 5
% 3.49/1.97  #Demod        : 84
% 3.49/1.97  #Tautology    : 81
% 3.49/1.97  #SimpNegUnit  : 1
% 3.49/1.97  #BackRed      : 12
% 3.49/1.97  
% 3.49/1.97  #Partial instantiations: 0
% 3.49/1.97  #Strategies tried      : 1
% 3.49/1.97  
% 3.49/1.97  Timing (in seconds)
% 3.49/1.97  ----------------------
% 3.49/1.98  Preprocessing        : 0.52
% 3.49/1.98  Parsing              : 0.28
% 3.49/1.98  CNF conversion       : 0.04
% 3.74/1.98  Main loop            : 0.51
% 3.74/1.98  Inferencing          : 0.20
% 3.74/1.98  Reduction            : 0.16
% 3.74/1.98  Demodulation         : 0.11
% 3.74/1.98  BG Simplification    : 0.03
% 3.74/1.98  Subsumption          : 0.07
% 3.74/1.98  Abstraction          : 0.02
% 3.74/1.98  MUC search           : 0.00
% 3.74/1.98  Cooper               : 0.00
% 3.74/1.98  Total                : 1.10
% 3.74/1.98  Index Insertion      : 0.00
% 3.74/1.98  Index Deletion       : 0.00
% 3.74/1.98  Index Matching       : 0.00
% 3.74/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
