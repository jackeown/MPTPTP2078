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
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 105 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_304,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_311,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_304])).

tff(c_18,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_529,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_538,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_529])).

tff(c_758,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1(k1_relset_1(A_100,B_101,C_102),k1_zfmisc_1(A_100))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_774,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_758])).

tff(c_780,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_774])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_788,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_780,c_12])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_808,plain,(
    k2_xboole_0(k1_relat_1('#skF_4'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_788,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(k2_xboole_0(A_47,B_49),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [A_50,B_51] : r1_tarski(A_50,k2_xboole_0(A_50,B_51)) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_3,B_4,B_51] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_51)) ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_851,plain,(
    ! [B_103] : r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0('#skF_2',B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_158])).

tff(c_870,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_851])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_897,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_870,c_20])).

tff(c_908,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_897])).

tff(c_883,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k5_relset_1(A_104,B_105,C_106,D_107) = k7_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_894,plain,(
    ! [D_107] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_107) = k7_relat_1('#skF_4',D_107) ),
    inference(resolution,[status(thm)],[c_36,c_883])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_952,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_32])).

tff(c_955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_908,c_952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:59:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.42  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.83/1.42  
% 2.83/1.42  %Foreground sorts:
% 2.83/1.42  
% 2.83/1.42  
% 2.83/1.42  %Background operators:
% 2.83/1.42  
% 2.83/1.42  
% 2.83/1.42  %Foreground operators:
% 2.83/1.42  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.83/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.83/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.42  
% 2.83/1.43  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.83/1.43  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.83/1.43  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.83/1.43  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.83/1.43  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.83/1.43  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.83/1.43  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.83/1.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.83/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.43  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.83/1.43  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.83/1.43  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.83/1.43  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.43  tff(c_304, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.43  tff(c_311, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_304])).
% 2.83/1.43  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.43  tff(c_76, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.43  tff(c_82, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_76])).
% 2.83/1.43  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_82])).
% 2.83/1.43  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.43  tff(c_50, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.43  tff(c_62, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.83/1.43  tff(c_529, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.43  tff(c_538, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_529])).
% 2.83/1.43  tff(c_758, plain, (![A_100, B_101, C_102]: (m1_subset_1(k1_relset_1(A_100, B_101, C_102), k1_zfmisc_1(A_100)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.43  tff(c_774, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_538, c_758])).
% 2.83/1.43  tff(c_780, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_774])).
% 2.83/1.43  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.43  tff(c_788, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_780, c_12])).
% 2.83/1.43  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.43  tff(c_808, plain, (k2_xboole_0(k1_relat_1('#skF_4'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_788, c_10])).
% 2.83/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.44  tff(c_121, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(k2_xboole_0(A_47, B_49), C_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.44  tff(c_136, plain, (![A_50, B_51]: (r1_tarski(A_50, k2_xboole_0(A_50, B_51)))), inference(resolution, [status(thm)], [c_6, c_121])).
% 2.83/1.44  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.44  tff(c_158, plain, (![A_3, B_4, B_51]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_51)))), inference(resolution, [status(thm)], [c_136, c_8])).
% 2.83/1.44  tff(c_851, plain, (![B_103]: (r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0('#skF_2', B_103)))), inference(superposition, [status(thm), theory('equality')], [c_808, c_158])).
% 2.83/1.44  tff(c_870, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_851])).
% 2.83/1.44  tff(c_20, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~r1_tarski(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.44  tff(c_897, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_870, c_20])).
% 2.83/1.44  tff(c_908, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_897])).
% 2.83/1.44  tff(c_883, plain, (![A_104, B_105, C_106, D_107]: (k5_relset_1(A_104, B_105, C_106, D_107)=k7_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.83/1.44  tff(c_894, plain, (![D_107]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_107)=k7_relat_1('#skF_4', D_107))), inference(resolution, [status(thm)], [c_36, c_883])).
% 2.83/1.44  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.44  tff(c_952, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_32])).
% 2.83/1.44  tff(c_955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_908, c_952])).
% 2.83/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  Inference rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Ref     : 0
% 2.83/1.44  #Sup     : 217
% 2.83/1.44  #Fact    : 0
% 2.83/1.44  #Define  : 0
% 2.83/1.44  #Split   : 6
% 2.83/1.44  #Chain   : 0
% 2.83/1.44  #Close   : 0
% 2.83/1.44  
% 2.83/1.44  Ordering : KBO
% 2.83/1.44  
% 2.83/1.44  Simplification rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Subsume      : 42
% 2.83/1.44  #Demod        : 90
% 2.83/1.44  #Tautology    : 87
% 2.83/1.44  #SimpNegUnit  : 0
% 2.83/1.44  #BackRed      : 1
% 2.83/1.44  
% 2.83/1.44  #Partial instantiations: 0
% 2.83/1.44  #Strategies tried      : 1
% 2.83/1.44  
% 2.83/1.44  Timing (in seconds)
% 2.83/1.44  ----------------------
% 2.83/1.44  Preprocessing        : 0.31
% 2.83/1.44  Parsing              : 0.17
% 2.83/1.44  CNF conversion       : 0.02
% 2.83/1.44  Main loop            : 0.35
% 2.83/1.44  Inferencing          : 0.13
% 2.83/1.44  Reduction            : 0.11
% 2.83/1.44  Demodulation         : 0.09
% 2.83/1.44  BG Simplification    : 0.02
% 2.83/1.44  Subsumption          : 0.07
% 2.83/1.44  Abstraction          : 0.02
% 2.83/1.44  MUC search           : 0.00
% 2.83/1.44  Cooper               : 0.00
% 2.83/1.44  Total                : 0.70
% 2.83/1.44  Index Insertion      : 0.00
% 2.83/1.44  Index Deletion       : 0.00
% 2.83/1.44  Index Matching       : 0.00
% 2.83/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
