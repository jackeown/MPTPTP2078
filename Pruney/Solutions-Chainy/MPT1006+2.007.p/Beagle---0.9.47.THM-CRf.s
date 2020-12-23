%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 314 expanded)
%              Number of leaves         :   32 ( 122 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 572 expanded)
%              Number of equality atoms :   29 ( 209 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_95,plain,(
    ! [C_33] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_126,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_xboole_0(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [C_42] :
      ( v1_xboole_0(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_141,plain,(
    ! [C_45] :
      ( v1_xboole_0(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_149,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_141])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_155,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_171,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_18])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_170,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_20])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( v1_funct_2(B_24,k1_relat_1(B_24),A_23)
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_188,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_3','#skF_3',A_23)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_23)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_34])).

tff(c_192,plain,(
    ! [A_23] : v1_funct_2('#skF_3','#skF_3',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_171,c_169,c_188])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_165,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_14])).

tff(c_254,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k8_relset_1(A_53,B_54,C_55,D_56) = k10_relat_1(C_55,D_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_262,plain,(
    ! [A_53,B_54,D_56] : k8_relset_1(A_53,B_54,'#skF_3',D_56) = k10_relat_1('#skF_3',D_56) ),
    inference(resolution,[status(thm)],[c_165,c_254])).

tff(c_28,plain,(
    ! [B_21,C_22] :
      ( k8_relset_1(k1_xboole_0,B_21,C_22,B_21) = k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21)))
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    ! [B_21,C_22] :
      ( k8_relset_1(k1_xboole_0,B_21,C_22,B_21) = k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_350,plain,(
    ! [B_76,C_77] :
      ( k8_relset_1('#skF_3',B_76,C_77,B_76) = '#skF_3'
      | ~ m1_subset_1(C_77,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_77,'#skF_3',B_76)
      | ~ v1_funct_1(C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_155,c_155,c_45])).

tff(c_353,plain,(
    ! [B_76] :
      ( k8_relset_1('#skF_3',B_76,'#skF_3',B_76) = '#skF_3'
      | ~ v1_funct_2('#skF_3','#skF_3',B_76)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_165,c_350])).

tff(c_356,plain,(
    ! [B_76] : k10_relat_1('#skF_3',B_76) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_192,c_262,c_353])).

tff(c_38,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_164,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_38])).

tff(c_333,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_164])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.73  
% 2.79/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.74  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.74  
% 2.79/1.74  %Foreground sorts:
% 2.79/1.74  
% 2.79/1.74  
% 2.79/1.74  %Background operators:
% 2.79/1.74  
% 2.79/1.74  
% 2.79/1.74  %Foreground operators:
% 2.79/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.74  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.79/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.79/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.74  
% 2.86/1.76  tff(f_97, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.86/1.76  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.86/1.76  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.86/1.76  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.86/1.76  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.86/1.76  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.86/1.76  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.86/1.76  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.86/1.76  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.86/1.76  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.86/1.76  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.86/1.76  tff(f_76, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.86/1.76  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.76  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.76  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.76  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 2.86/1.76  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.76  tff(c_85, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.86/1.76  tff(c_95, plain, (![C_33]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_85])).
% 2.86/1.76  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_95])).
% 2.86/1.76  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.86/1.76  tff(c_126, plain, (![C_42, A_43, B_44]: (v1_xboole_0(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.76  tff(c_136, plain, (![C_42]: (v1_xboole_0(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_126])).
% 2.86/1.76  tff(c_141, plain, (![C_45]: (v1_xboole_0(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_136])).
% 2.86/1.76  tff(c_149, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_141])).
% 2.86/1.76  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.86/1.76  tff(c_155, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_149, c_4])).
% 2.86/1.76  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.76  tff(c_171, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_6])).
% 2.86/1.76  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.76  tff(c_169, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_18])).
% 2.86/1.76  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.76  tff(c_170, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_20])).
% 2.86/1.76  tff(c_34, plain, (![B_24, A_23]: (v1_funct_2(B_24, k1_relat_1(B_24), A_23) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.76  tff(c_188, plain, (![A_23]: (v1_funct_2('#skF_3', '#skF_3', A_23) | ~r1_tarski(k2_relat_1('#skF_3'), A_23) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_34])).
% 2.86/1.76  tff(c_192, plain, (![A_23]: (v1_funct_2('#skF_3', '#skF_3', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_171, c_169, c_188])).
% 2.86/1.76  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.76  tff(c_165, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_14])).
% 2.86/1.76  tff(c_254, plain, (![A_53, B_54, C_55, D_56]: (k8_relset_1(A_53, B_54, C_55, D_56)=k10_relat_1(C_55, D_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.76  tff(c_262, plain, (![A_53, B_54, D_56]: (k8_relset_1(A_53, B_54, '#skF_3', D_56)=k10_relat_1('#skF_3', D_56))), inference(resolution, [status(thm)], [c_165, c_254])).
% 2.86/1.76  tff(c_28, plain, (![B_21, C_22]: (k8_relset_1(k1_xboole_0, B_21, C_22, B_21)=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))) | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.86/1.76  tff(c_45, plain, (![B_21, C_22]: (k8_relset_1(k1_xboole_0, B_21, C_22, B_21)=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~v1_funct_1(C_22))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 2.86/1.76  tff(c_350, plain, (![B_76, C_77]: (k8_relset_1('#skF_3', B_76, C_77, B_76)='#skF_3' | ~m1_subset_1(C_77, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_77, '#skF_3', B_76) | ~v1_funct_1(C_77))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_155, c_155, c_45])).
% 2.86/1.76  tff(c_353, plain, (![B_76]: (k8_relset_1('#skF_3', B_76, '#skF_3', B_76)='#skF_3' | ~v1_funct_2('#skF_3', '#skF_3', B_76) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_165, c_350])).
% 2.86/1.76  tff(c_356, plain, (![B_76]: (k10_relat_1('#skF_3', B_76)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_192, c_262, c_353])).
% 2.86/1.76  tff(c_38, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.76  tff(c_164, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_38])).
% 2.86/1.76  tff(c_333, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_164])).
% 2.86/1.76  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_333])).
% 2.86/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.76  
% 2.86/1.76  Inference rules
% 2.86/1.76  ----------------------
% 2.86/1.76  #Ref     : 0
% 2.86/1.76  #Sup     : 69
% 2.86/1.76  #Fact    : 0
% 2.86/1.76  #Define  : 0
% 2.86/1.76  #Split   : 0
% 2.86/1.76  #Chain   : 0
% 2.86/1.76  #Close   : 0
% 2.86/1.76  
% 2.86/1.76  Ordering : KBO
% 2.86/1.76  
% 2.86/1.76  Simplification rules
% 2.86/1.76  ----------------------
% 2.86/1.76  #Subsume      : 9
% 2.86/1.76  #Demod        : 63
% 2.86/1.76  #Tautology    : 46
% 2.86/1.76  #SimpNegUnit  : 0
% 2.86/1.76  #BackRed      : 20
% 2.86/1.76  
% 2.86/1.76  #Partial instantiations: 0
% 2.86/1.76  #Strategies tried      : 1
% 2.86/1.76  
% 2.86/1.76  Timing (in seconds)
% 2.86/1.76  ----------------------
% 2.86/1.76  Preprocessing        : 0.49
% 2.86/1.76  Parsing              : 0.26
% 2.86/1.76  CNF conversion       : 0.03
% 2.86/1.76  Main loop            : 0.33
% 2.86/1.77  Inferencing          : 0.11
% 2.86/1.77  Reduction            : 0.11
% 2.86/1.77  Demodulation         : 0.08
% 2.86/1.77  BG Simplification    : 0.02
% 2.86/1.77  Subsumption          : 0.06
% 2.86/1.77  Abstraction          : 0.02
% 2.86/1.77  MUC search           : 0.00
% 2.86/1.77  Cooper               : 0.00
% 2.86/1.77  Total                : 0.88
% 2.86/1.77  Index Insertion      : 0.00
% 2.86/1.77  Index Deletion       : 0.00
% 2.86/1.77  Index Matching       : 0.00
% 2.86/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
