%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 107 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 141 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_92,negated_conjecture,(
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

tff(f_87,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_41,A_1] :
      ( r1_tarski(A_41,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_41,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_100,plain,(
    ! [A_43,A_44] :
      ( r1_tarski(A_43,A_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_44)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_96])).

tff(c_108,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_42,plain,(
    ! [A_27] : k6_relat_1(A_27) = k6_partfun1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [A_18] : k1_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_24])).

tff(c_30,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30])).

tff(c_32,plain,(
    ! [A_21] : v4_relat_1(k6_relat_1(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [A_21] : v4_relat_1(k6_partfun1(A_21),A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_126,plain,(
    ! [C_49,B_50,A_51] :
      ( v4_relat_1(C_49,B_50)
      | ~ v4_relat_1(C_49,A_51)
      | ~ v1_relat_1(C_49)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [A_21,B_50] :
      ( v4_relat_1(k6_partfun1(A_21),B_50)
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ r1_tarski(A_21,B_50) ) ),
    inference(resolution,[status(thm)],[c_48,c_126])).

tff(c_132,plain,(
    ! [A_52,B_53] :
      ( v4_relat_1(k6_partfun1(A_52),B_53)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_128])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [A_52,B_53] :
      ( k7_relat_1(k6_partfun1(A_52),B_53) = k6_partfun1(A_52)
      | ~ v1_relat_1(k6_partfun1(A_52))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_132,c_20])).

tff(c_143,plain,(
    ! [A_52,B_53] :
      ( k7_relat_1(k6_partfun1(A_52),B_53) = k6_partfun1(A_52)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_137])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_partfun1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28])).

tff(c_190,plain,(
    ! [A_62,B_63] :
      ( k10_relat_1(A_62,k1_relat_1(B_63)) = k1_relat_1(k5_relat_1(A_62,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_199,plain,(
    ! [A_62,A_18] :
      ( k1_relat_1(k5_relat_1(A_62,k6_partfun1(A_18))) = k10_relat_1(A_62,A_18)
      | ~ v1_relat_1(k6_partfun1(A_18))
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_190])).

tff(c_232,plain,(
    ! [A_65,A_66] :
      ( k1_relat_1(k5_relat_1(A_65,k6_partfun1(A_66))) = k10_relat_1(A_65,A_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_199])).

tff(c_245,plain,(
    ! [A_66,A_19] :
      ( k1_relat_1(k7_relat_1(k6_partfun1(A_66),A_19)) = k10_relat_1(k6_partfun1(A_19),A_66)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_232])).

tff(c_250,plain,(
    ! [A_67,A_68] : k1_relat_1(k7_relat_1(k6_partfun1(A_67),A_68)) = k10_relat_1(k6_partfun1(A_68),A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_49,c_245])).

tff(c_265,plain,(
    ! [B_53,A_52] :
      ( k10_relat_1(k6_partfun1(B_53),A_52) = k1_relat_1(k6_partfun1(A_52))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_250])).

tff(c_272,plain,(
    ! [B_53,A_52] :
      ( k10_relat_1(k6_partfun1(B_53),A_52) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_265])).

tff(c_40,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_864,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k8_relset_1(A_107,B_108,C_109,D_110) = k10_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_867,plain,(
    ! [A_26,D_110] : k8_relset_1(A_26,A_26,k6_partfun1(A_26),D_110) = k10_relat_1(k6_partfun1(A_26),D_110) ),
    inference(resolution,[status(thm)],[c_40,c_864])).

tff(c_44,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_868,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_44])).

tff(c_886,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_868])).

tff(c_892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.57  
% 2.81/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.58  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.81/1.58  
% 2.81/1.58  %Foreground sorts:
% 2.81/1.58  
% 2.81/1.58  
% 2.81/1.58  %Background operators:
% 2.81/1.58  
% 2.81/1.58  
% 2.81/1.58  %Foreground operators:
% 2.81/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.81/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.81/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.58  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.81/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.58  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.81/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.81/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.81/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.58  
% 2.81/1.59  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.81/1.59  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.81/1.59  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.59  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.81/1.59  tff(f_87, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.81/1.59  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.81/1.59  tff(f_77, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.81/1.59  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.81/1.59  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.81/1.59  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.81/1.59  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.81/1.59  tff(f_85, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.81/1.59  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.81/1.59  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.59  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.59  tff(c_92, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.59  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.59  tff(c_96, plain, (![A_41, A_1]: (r1_tarski(A_41, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_41, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.81/1.59  tff(c_100, plain, (![A_43, A_44]: (r1_tarski(A_43, A_44) | ~m1_subset_1(A_43, k1_zfmisc_1(A_44)))), inference(negUnitSimplification, [status(thm)], [c_14, c_96])).
% 2.81/1.59  tff(c_108, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_100])).
% 2.81/1.59  tff(c_42, plain, (![A_27]: (k6_relat_1(A_27)=k6_partfun1(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.59  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.59  tff(c_52, plain, (![A_18]: (k1_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_24])).
% 2.81/1.59  tff(c_30, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.59  tff(c_49, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30])).
% 2.81/1.59  tff(c_32, plain, (![A_21]: (v4_relat_1(k6_relat_1(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.59  tff(c_48, plain, (![A_21]: (v4_relat_1(k6_partfun1(A_21), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 2.81/1.59  tff(c_126, plain, (![C_49, B_50, A_51]: (v4_relat_1(C_49, B_50) | ~v4_relat_1(C_49, A_51) | ~v1_relat_1(C_49) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.59  tff(c_128, plain, (![A_21, B_50]: (v4_relat_1(k6_partfun1(A_21), B_50) | ~v1_relat_1(k6_partfun1(A_21)) | ~r1_tarski(A_21, B_50))), inference(resolution, [status(thm)], [c_48, c_126])).
% 2.81/1.59  tff(c_132, plain, (![A_52, B_53]: (v4_relat_1(k6_partfun1(A_52), B_53) | ~r1_tarski(A_52, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_128])).
% 2.81/1.59  tff(c_20, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.59  tff(c_137, plain, (![A_52, B_53]: (k7_relat_1(k6_partfun1(A_52), B_53)=k6_partfun1(A_52) | ~v1_relat_1(k6_partfun1(A_52)) | ~r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_132, c_20])).
% 2.81/1.59  tff(c_143, plain, (![A_52, B_53]: (k7_relat_1(k6_partfun1(A_52), B_53)=k6_partfun1(A_52) | ~r1_tarski(A_52, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_137])).
% 2.81/1.59  tff(c_28, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.59  tff(c_50, plain, (![A_19, B_20]: (k5_relat_1(k6_partfun1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28])).
% 2.81/1.59  tff(c_190, plain, (![A_62, B_63]: (k10_relat_1(A_62, k1_relat_1(B_63))=k1_relat_1(k5_relat_1(A_62, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.59  tff(c_199, plain, (![A_62, A_18]: (k1_relat_1(k5_relat_1(A_62, k6_partfun1(A_18)))=k10_relat_1(A_62, A_18) | ~v1_relat_1(k6_partfun1(A_18)) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_52, c_190])).
% 2.81/1.59  tff(c_232, plain, (![A_65, A_66]: (k1_relat_1(k5_relat_1(A_65, k6_partfun1(A_66)))=k10_relat_1(A_65, A_66) | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_199])).
% 2.81/1.59  tff(c_245, plain, (![A_66, A_19]: (k1_relat_1(k7_relat_1(k6_partfun1(A_66), A_19))=k10_relat_1(k6_partfun1(A_19), A_66) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_232])).
% 2.81/1.59  tff(c_250, plain, (![A_67, A_68]: (k1_relat_1(k7_relat_1(k6_partfun1(A_67), A_68))=k10_relat_1(k6_partfun1(A_68), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_49, c_245])).
% 2.81/1.59  tff(c_265, plain, (![B_53, A_52]: (k10_relat_1(k6_partfun1(B_53), A_52)=k1_relat_1(k6_partfun1(A_52)) | ~r1_tarski(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_143, c_250])).
% 2.81/1.59  tff(c_272, plain, (![B_53, A_52]: (k10_relat_1(k6_partfun1(B_53), A_52)=A_52 | ~r1_tarski(A_52, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_265])).
% 2.81/1.59  tff(c_40, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.59  tff(c_864, plain, (![A_107, B_108, C_109, D_110]: (k8_relset_1(A_107, B_108, C_109, D_110)=k10_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.59  tff(c_867, plain, (![A_26, D_110]: (k8_relset_1(A_26, A_26, k6_partfun1(A_26), D_110)=k10_relat_1(k6_partfun1(A_26), D_110))), inference(resolution, [status(thm)], [c_40, c_864])).
% 2.81/1.59  tff(c_44, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.59  tff(c_868, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_867, c_44])).
% 2.81/1.59  tff(c_886, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_272, c_868])).
% 2.81/1.59  tff(c_892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_886])).
% 2.81/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.59  
% 2.81/1.59  Inference rules
% 2.81/1.59  ----------------------
% 2.81/1.59  #Ref     : 0
% 2.81/1.59  #Sup     : 178
% 2.81/1.59  #Fact    : 0
% 2.81/1.59  #Define  : 0
% 2.81/1.59  #Split   : 0
% 2.81/1.59  #Chain   : 0
% 2.81/1.59  #Close   : 0
% 2.81/1.59  
% 2.81/1.59  Ordering : KBO
% 2.81/1.59  
% 2.81/1.59  Simplification rules
% 2.81/1.59  ----------------------
% 2.81/1.59  #Subsume      : 8
% 2.81/1.59  #Demod        : 114
% 2.81/1.59  #Tautology    : 101
% 2.81/1.59  #SimpNegUnit  : 1
% 2.81/1.59  #BackRed      : 1
% 2.81/1.59  
% 2.81/1.59  #Partial instantiations: 0
% 2.81/1.59  #Strategies tried      : 1
% 2.81/1.59  
% 2.81/1.59  Timing (in seconds)
% 2.81/1.59  ----------------------
% 2.81/1.59  Preprocessing        : 0.40
% 2.81/1.59  Parsing              : 0.23
% 2.81/1.59  CNF conversion       : 0.02
% 2.81/1.59  Main loop            : 0.32
% 2.81/1.59  Inferencing          : 0.13
% 2.81/1.59  Reduction            : 0.10
% 2.81/1.59  Demodulation         : 0.07
% 2.81/1.59  BG Simplification    : 0.02
% 2.81/1.59  Subsumption          : 0.05
% 2.81/1.59  Abstraction          : 0.02
% 2.81/1.59  MUC search           : 0.00
% 2.81/1.59  Cooper               : 0.00
% 2.81/1.59  Total                : 0.75
% 2.81/1.59  Index Insertion      : 0.00
% 2.81/1.59  Index Deletion       : 0.00
% 2.81/1.59  Index Matching       : 0.00
% 2.81/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
