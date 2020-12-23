%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 109 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 143 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_83,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_40,A_1] :
      ( r1_tarski(A_40,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_40,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_98,plain,(
    ! [A_42,A_43] :
      ( r1_tarski(A_42,A_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(A_43)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_94])).

tff(c_106,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_40,plain,(
    ! [A_27] : k6_relat_1(A_27) = k6_partfun1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_51,plain,(
    ! [A_18] : k1_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24])).

tff(c_30,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_32,plain,(
    ! [A_21] : v4_relat_1(k6_relat_1(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ! [A_21] : v4_relat_1(k6_partfun1(A_21),A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_133,plain,(
    ! [C_50,B_51,A_52] :
      ( v4_relat_1(C_50,B_51)
      | ~ v4_relat_1(C_50,A_52)
      | ~ v1_relat_1(C_50)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_135,plain,(
    ! [A_21,B_51] :
      ( v4_relat_1(k6_partfun1(A_21),B_51)
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ r1_tarski(A_21,B_51) ) ),
    inference(resolution,[status(thm)],[c_47,c_133])).

tff(c_139,plain,(
    ! [A_53,B_54] :
      ( v4_relat_1(k6_partfun1(A_53),B_54)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_135])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_144,plain,(
    ! [A_53,B_54] :
      ( k7_relat_1(k6_partfun1(A_53),B_54) = k6_partfun1(A_53)
      | ~ v1_relat_1(k6_partfun1(A_53))
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_139,c_20])).

tff(c_150,plain,(
    ! [A_53,B_54] :
      ( k7_relat_1(k6_partfun1(A_53),B_54) = k6_partfun1(A_53)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_144])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_49,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_partfun1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28])).

tff(c_216,plain,(
    ! [A_62,B_63] :
      ( k10_relat_1(A_62,k1_relat_1(B_63)) = k1_relat_1(k5_relat_1(A_62,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_225,plain,(
    ! [A_62,A_18] :
      ( k1_relat_1(k5_relat_1(A_62,k6_partfun1(A_18))) = k10_relat_1(A_62,A_18)
      | ~ v1_relat_1(k6_partfun1(A_18))
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_216])).

tff(c_230,plain,(
    ! [A_64,A_65] :
      ( k1_relat_1(k5_relat_1(A_64,k6_partfun1(A_65))) = k10_relat_1(A_64,A_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_225])).

tff(c_243,plain,(
    ! [A_65,A_19] :
      ( k1_relat_1(k7_relat_1(k6_partfun1(A_65),A_19)) = k10_relat_1(k6_partfun1(A_19),A_65)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_230])).

tff(c_248,plain,(
    ! [A_66,A_67] : k1_relat_1(k7_relat_1(k6_partfun1(A_66),A_67)) = k10_relat_1(k6_partfun1(A_67),A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_243])).

tff(c_263,plain,(
    ! [B_54,A_53] :
      ( k10_relat_1(k6_partfun1(B_54),A_53) = k1_relat_1(k6_partfun1(A_53))
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_248])).

tff(c_270,plain,(
    ! [B_54,A_53] :
      ( k10_relat_1(k6_partfun1(B_54),A_53) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_263])).

tff(c_38,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_45,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_731,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_734,plain,(
    ! [A_26,D_98] : k8_relset_1(A_26,A_26,k6_partfun1(A_26),D_98) = k10_relat_1(k6_partfun1(A_26),D_98) ),
    inference(resolution,[status(thm)],[c_45,c_731])).

tff(c_42,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_735,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_42])).

tff(c_753,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_735])).

tff(c_759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.43  
% 2.59/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.59/1.43  
% 2.59/1.43  %Foreground sorts:
% 2.59/1.43  
% 2.59/1.43  
% 2.59/1.43  %Background operators:
% 2.59/1.43  
% 2.59/1.43  
% 2.59/1.43  %Foreground operators:
% 2.59/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.59/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.59/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.59/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.59/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.59/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.59/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.59/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.59/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.43  
% 2.59/1.45  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.59/1.45  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.59/1.45  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.59/1.45  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.59/1.45  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.59/1.45  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.59/1.45  tff(f_77, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.59/1.45  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.59/1.45  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.59/1.45  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.59/1.45  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.59/1.45  tff(f_83, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.59/1.45  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.59/1.45  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.45  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.45  tff(c_90, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | v1_xboole_0(B_41) | ~m1_subset_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.45  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.45  tff(c_94, plain, (![A_40, A_1]: (r1_tarski(A_40, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_40, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.59/1.45  tff(c_98, plain, (![A_42, A_43]: (r1_tarski(A_42, A_43) | ~m1_subset_1(A_42, k1_zfmisc_1(A_43)))), inference(negUnitSimplification, [status(thm)], [c_14, c_94])).
% 2.59/1.45  tff(c_106, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_98])).
% 2.59/1.45  tff(c_40, plain, (![A_27]: (k6_relat_1(A_27)=k6_partfun1(A_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.45  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.45  tff(c_51, plain, (![A_18]: (k1_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24])).
% 2.59/1.45  tff(c_30, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.59/1.45  tff(c_48, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 2.59/1.45  tff(c_32, plain, (![A_21]: (v4_relat_1(k6_relat_1(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.59/1.45  tff(c_47, plain, (![A_21]: (v4_relat_1(k6_partfun1(A_21), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 2.59/1.45  tff(c_133, plain, (![C_50, B_51, A_52]: (v4_relat_1(C_50, B_51) | ~v4_relat_1(C_50, A_52) | ~v1_relat_1(C_50) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.45  tff(c_135, plain, (![A_21, B_51]: (v4_relat_1(k6_partfun1(A_21), B_51) | ~v1_relat_1(k6_partfun1(A_21)) | ~r1_tarski(A_21, B_51))), inference(resolution, [status(thm)], [c_47, c_133])).
% 2.59/1.45  tff(c_139, plain, (![A_53, B_54]: (v4_relat_1(k6_partfun1(A_53), B_54) | ~r1_tarski(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_135])).
% 2.59/1.45  tff(c_20, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.59/1.45  tff(c_144, plain, (![A_53, B_54]: (k7_relat_1(k6_partfun1(A_53), B_54)=k6_partfun1(A_53) | ~v1_relat_1(k6_partfun1(A_53)) | ~r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_139, c_20])).
% 2.59/1.45  tff(c_150, plain, (![A_53, B_54]: (k7_relat_1(k6_partfun1(A_53), B_54)=k6_partfun1(A_53) | ~r1_tarski(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_144])).
% 2.59/1.45  tff(c_28, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.45  tff(c_49, plain, (![A_19, B_20]: (k5_relat_1(k6_partfun1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28])).
% 2.59/1.45  tff(c_216, plain, (![A_62, B_63]: (k10_relat_1(A_62, k1_relat_1(B_63))=k1_relat_1(k5_relat_1(A_62, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.45  tff(c_225, plain, (![A_62, A_18]: (k1_relat_1(k5_relat_1(A_62, k6_partfun1(A_18)))=k10_relat_1(A_62, A_18) | ~v1_relat_1(k6_partfun1(A_18)) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_51, c_216])).
% 2.59/1.45  tff(c_230, plain, (![A_64, A_65]: (k1_relat_1(k5_relat_1(A_64, k6_partfun1(A_65)))=k10_relat_1(A_64, A_65) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_225])).
% 2.59/1.45  tff(c_243, plain, (![A_65, A_19]: (k1_relat_1(k7_relat_1(k6_partfun1(A_65), A_19))=k10_relat_1(k6_partfun1(A_19), A_65) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_230])).
% 2.59/1.45  tff(c_248, plain, (![A_66, A_67]: (k1_relat_1(k7_relat_1(k6_partfun1(A_66), A_67))=k10_relat_1(k6_partfun1(A_67), A_66))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_243])).
% 2.59/1.45  tff(c_263, plain, (![B_54, A_53]: (k10_relat_1(k6_partfun1(B_54), A_53)=k1_relat_1(k6_partfun1(A_53)) | ~r1_tarski(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_150, c_248])).
% 2.59/1.45  tff(c_270, plain, (![B_54, A_53]: (k10_relat_1(k6_partfun1(B_54), A_53)=A_53 | ~r1_tarski(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_263])).
% 2.59/1.45  tff(c_38, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.59/1.45  tff(c_45, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 2.59/1.45  tff(c_731, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.45  tff(c_734, plain, (![A_26, D_98]: (k8_relset_1(A_26, A_26, k6_partfun1(A_26), D_98)=k10_relat_1(k6_partfun1(A_26), D_98))), inference(resolution, [status(thm)], [c_45, c_731])).
% 2.59/1.45  tff(c_42, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.45  tff(c_735, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_734, c_42])).
% 2.59/1.45  tff(c_753, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_270, c_735])).
% 2.59/1.45  tff(c_759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_753])).
% 2.59/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.45  
% 2.59/1.45  Inference rules
% 2.59/1.45  ----------------------
% 2.59/1.45  #Ref     : 0
% 2.59/1.45  #Sup     : 149
% 2.59/1.45  #Fact    : 0
% 2.59/1.45  #Define  : 0
% 2.59/1.45  #Split   : 0
% 2.59/1.45  #Chain   : 0
% 2.59/1.45  #Close   : 0
% 2.59/1.45  
% 2.59/1.45  Ordering : KBO
% 2.59/1.45  
% 2.59/1.45  Simplification rules
% 2.59/1.45  ----------------------
% 2.59/1.45  #Subsume      : 1
% 2.59/1.45  #Demod        : 85
% 2.59/1.45  #Tautology    : 89
% 2.59/1.45  #SimpNegUnit  : 1
% 2.59/1.45  #BackRed      : 1
% 2.59/1.45  
% 2.59/1.45  #Partial instantiations: 0
% 2.59/1.45  #Strategies tried      : 1
% 2.59/1.45  
% 2.59/1.45  Timing (in seconds)
% 2.59/1.45  ----------------------
% 2.59/1.45  Preprocessing        : 0.34
% 2.59/1.45  Parsing              : 0.18
% 2.59/1.45  CNF conversion       : 0.03
% 2.59/1.45  Main loop            : 0.30
% 2.59/1.45  Inferencing          : 0.12
% 2.59/1.45  Reduction            : 0.09
% 2.59/1.45  Demodulation         : 0.07
% 2.59/1.45  BG Simplification    : 0.02
% 2.59/1.45  Subsumption          : 0.05
% 2.59/1.45  Abstraction          : 0.02
% 2.59/1.45  MUC search           : 0.00
% 2.59/1.45  Cooper               : 0.00
% 2.59/1.45  Total                : 0.67
% 2.59/1.45  Index Insertion      : 0.00
% 2.59/1.45  Index Deletion       : 0.00
% 2.59/1.45  Index Matching       : 0.00
% 2.59/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
