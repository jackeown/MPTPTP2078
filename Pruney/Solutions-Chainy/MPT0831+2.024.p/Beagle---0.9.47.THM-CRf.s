%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:35 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :   63 (  74 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 110 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_542,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( r2_relset_1(A_129,B_130,C_131,C_131)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_575,plain,(
    ! [C_143] :
      ( r2_relset_1('#skF_2','#skF_1',C_143,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_542])).

tff(c_582,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_575])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_128,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_134])).

tff(c_70,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_353,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(k2_zfmisc_1(A_89,C_90),k2_zfmisc_1(B_91,C_90))
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_657,plain,(
    ! [A_149,C_150,B_151] :
      ( k2_xboole_0(k2_zfmisc_1(A_149,C_150),k2_zfmisc_1(B_151,C_150)) = k2_zfmisc_1(B_151,C_150)
      | ~ r1_tarski(A_149,B_151) ) ),
    inference(resolution,[status(thm)],[c_353,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,k2_xboole_0(C_42,B_43))
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_41,A_1,B_2] :
      ( r1_tarski(A_41,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_41,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_3912,plain,(
    ! [A_300,B_301,C_302,A_303] :
      ( r1_tarski(A_300,k2_zfmisc_1(B_301,C_302))
      | ~ r1_tarski(A_300,k2_zfmisc_1(A_303,C_302))
      | ~ r1_tarski(A_303,B_301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_126])).

tff(c_3925,plain,(
    ! [B_304] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_304,'#skF_1'))
      | ~ r1_tarski('#skF_2',B_304) ) ),
    inference(resolution,[status(thm)],[c_78,c_3912])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_198,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_206,plain,(
    ! [A_11,A_54,B_55] :
      ( v4_relat_1(A_11,A_54)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_14,c_198])).

tff(c_4024,plain,(
    ! [B_305] :
      ( v4_relat_1('#skF_4',B_305)
      | ~ r1_tarski('#skF_2',B_305) ) ),
    inference(resolution,[status(thm)],[c_3925,c_206])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4027,plain,(
    ! [B_305] :
      ( k7_relat_1('#skF_4',B_305) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_305) ) ),
    inference(resolution,[status(thm)],[c_4024,c_20])).

tff(c_4031,plain,(
    ! [B_306] :
      ( k7_relat_1('#skF_4',B_306) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_4027])).

tff(c_4066,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_4031])).

tff(c_451,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k5_relset_1(A_106,B_107,C_108,D_109) = k7_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_458,plain,(
    ! [D_109] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_109) = k7_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_34,c_451])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_473,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_30])).

tff(c_4067,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4066,c_473])).

tff(c_4070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_4067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.20  
% 5.54/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.20  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.54/2.20  
% 5.54/2.20  %Foreground sorts:
% 5.54/2.20  
% 5.54/2.20  
% 5.54/2.20  %Background operators:
% 5.54/2.20  
% 5.54/2.20  
% 5.54/2.20  %Foreground operators:
% 5.54/2.20  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 5.54/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.20  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.54/2.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.54/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.54/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.54/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.54/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.54/2.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.54/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.54/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.54/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.54/2.20  tff('#skF_4', type, '#skF_4': $i).
% 5.54/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.54/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.54/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.54/2.20  
% 5.86/2.22  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 5.86/2.22  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.86/2.22  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.86/2.22  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.86/2.22  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.86/2.22  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 5.86/2.22  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.86/2.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.86/2.22  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.86/2.22  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.86/2.22  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.86/2.22  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 5.86/2.22  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.22  tff(c_542, plain, (![A_129, B_130, C_131, D_132]: (r2_relset_1(A_129, B_130, C_131, C_131) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.86/2.22  tff(c_575, plain, (![C_143]: (r2_relset_1('#skF_2', '#skF_1', C_143, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_34, c_542])).
% 5.86/2.22  tff(c_582, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_575])).
% 5.86/2.22  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.22  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.86/2.22  tff(c_128, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.86/2.22  tff(c_134, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_128])).
% 5.86/2.22  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_134])).
% 5.86/2.22  tff(c_70, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.86/2.22  tff(c_78, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_70])).
% 5.86/2.22  tff(c_353, plain, (![A_89, C_90, B_91]: (r1_tarski(k2_zfmisc_1(A_89, C_90), k2_zfmisc_1(B_91, C_90)) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.86/2.22  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.86/2.22  tff(c_657, plain, (![A_149, C_150, B_151]: (k2_xboole_0(k2_zfmisc_1(A_149, C_150), k2_zfmisc_1(B_151, C_150))=k2_zfmisc_1(B_151, C_150) | ~r1_tarski(A_149, B_151))), inference(resolution, [status(thm)], [c_353, c_6])).
% 5.86/2.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.86/2.22  tff(c_111, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, k2_xboole_0(C_42, B_43)) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.86/2.22  tff(c_126, plain, (![A_41, A_1, B_2]: (r1_tarski(A_41, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_41, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_111])).
% 5.86/2.22  tff(c_3912, plain, (![A_300, B_301, C_302, A_303]: (r1_tarski(A_300, k2_zfmisc_1(B_301, C_302)) | ~r1_tarski(A_300, k2_zfmisc_1(A_303, C_302)) | ~r1_tarski(A_303, B_301))), inference(superposition, [status(thm), theory('equality')], [c_657, c_126])).
% 5.86/2.22  tff(c_3925, plain, (![B_304]: (r1_tarski('#skF_4', k2_zfmisc_1(B_304, '#skF_1')) | ~r1_tarski('#skF_2', B_304))), inference(resolution, [status(thm)], [c_78, c_3912])).
% 5.86/2.22  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.86/2.22  tff(c_198, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.86/2.22  tff(c_206, plain, (![A_11, A_54, B_55]: (v4_relat_1(A_11, A_54) | ~r1_tarski(A_11, k2_zfmisc_1(A_54, B_55)))), inference(resolution, [status(thm)], [c_14, c_198])).
% 5.86/2.22  tff(c_4024, plain, (![B_305]: (v4_relat_1('#skF_4', B_305) | ~r1_tarski('#skF_2', B_305))), inference(resolution, [status(thm)], [c_3925, c_206])).
% 5.86/2.22  tff(c_20, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.86/2.22  tff(c_4027, plain, (![B_305]: (k7_relat_1('#skF_4', B_305)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_305))), inference(resolution, [status(thm)], [c_4024, c_20])).
% 5.86/2.22  tff(c_4031, plain, (![B_306]: (k7_relat_1('#skF_4', B_306)='#skF_4' | ~r1_tarski('#skF_2', B_306))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_4027])).
% 5.86/2.22  tff(c_4066, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_4031])).
% 5.86/2.22  tff(c_451, plain, (![A_106, B_107, C_108, D_109]: (k5_relset_1(A_106, B_107, C_108, D_109)=k7_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.86/2.22  tff(c_458, plain, (![D_109]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_109)=k7_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_34, c_451])).
% 5.86/2.22  tff(c_30, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.22  tff(c_473, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_30])).
% 5.86/2.22  tff(c_4067, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4066, c_473])).
% 5.86/2.22  tff(c_4070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_582, c_4067])).
% 5.86/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.22  
% 5.86/2.22  Inference rules
% 5.86/2.22  ----------------------
% 5.86/2.22  #Ref     : 0
% 5.86/2.22  #Sup     : 1133
% 5.86/2.22  #Fact    : 0
% 5.86/2.22  #Define  : 0
% 5.86/2.22  #Split   : 4
% 5.86/2.22  #Chain   : 0
% 5.86/2.22  #Close   : 0
% 5.86/2.22  
% 5.86/2.22  Ordering : KBO
% 5.86/2.22  
% 5.86/2.22  Simplification rules
% 5.86/2.22  ----------------------
% 5.86/2.22  #Subsume      : 350
% 5.86/2.22  #Demod        : 231
% 5.86/2.22  #Tautology    : 232
% 5.86/2.22  #SimpNegUnit  : 0
% 5.86/2.22  #BackRed      : 2
% 5.86/2.22  
% 5.86/2.22  #Partial instantiations: 0
% 5.86/2.22  #Strategies tried      : 1
% 5.86/2.22  
% 5.86/2.22  Timing (in seconds)
% 5.86/2.22  ----------------------
% 5.86/2.23  Preprocessing        : 0.34
% 5.86/2.23  Parsing              : 0.18
% 5.86/2.23  CNF conversion       : 0.02
% 5.86/2.23  Main loop            : 1.10
% 5.86/2.23  Inferencing          : 0.35
% 5.86/2.23  Reduction            : 0.36
% 5.86/2.23  Demodulation         : 0.28
% 5.86/2.23  BG Simplification    : 0.04
% 5.86/2.23  Subsumption          : 0.26
% 5.86/2.23  Abstraction          : 0.05
% 5.86/2.23  MUC search           : 0.00
% 5.86/2.23  Cooper               : 0.00
% 5.86/2.23  Total                : 1.47
% 5.86/2.23  Index Insertion      : 0.00
% 5.86/2.23  Index Deletion       : 0.00
% 5.86/2.23  Index Matching       : 0.00
% 5.86/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
