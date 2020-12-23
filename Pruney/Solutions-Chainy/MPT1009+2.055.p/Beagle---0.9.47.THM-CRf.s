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

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 228 expanded)
%              Number of leaves         :   42 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 446 expanded)
%              Number of equality atoms :   44 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_106,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_106])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_127,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_119,c_38])).

tff(c_143,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_216,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_229,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_216])).

tff(c_301,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v4_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_381,plain,(
    ! [B_105,B_106] :
      ( k1_tarski(B_105) = k1_relat_1(B_106)
      | k1_relat_1(B_106) = k1_xboole_0
      | ~ v4_relat_1(B_106,k1_tarski(B_105))
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_301,c_8])).

tff(c_384,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_229,c_381])).

tff(c_391,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_384])).

tff(c_392,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_391])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(k1_funct_1(B_25,A_24)) = k2_relat_1(B_25)
      | k1_tarski(A_24) != k1_relat_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_428,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_54])).

tff(c_48,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k7_relset_1(A_32,B_33,C_34,D_35) = k9_relat_1(C_34,D_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_531,plain,(
    ! [D_35] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_35) = k9_relat_1('#skF_4',D_35) ),
    inference(resolution,[status(thm)],[c_428,c_48])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_426,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_50])).

tff(c_547,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_426])).

tff(c_559,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_547])).

tff(c_561,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_58,c_392,c_559])).

tff(c_564,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_561])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_564])).

tff(c_569,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_580,plain,(
    ! [A_9] : r1_tarski('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_87])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_582,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_569,c_32])).

tff(c_581,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_14])).

tff(c_722,plain,(
    ! [C_146,A_147,B_148] :
      ( v4_relat_1(C_146,A_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_733,plain,(
    ! [A_149] : v4_relat_1('#skF_4',A_149) ),
    inference(resolution,[status(thm)],[c_581,c_722])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_736,plain,(
    ! [A_149] :
      ( k7_relat_1('#skF_4',A_149) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_733,c_30])).

tff(c_750,plain,(
    ! [A_152] : k7_relat_1('#skF_4',A_152) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_736])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_755,plain,(
    ! [A_152] :
      ( k9_relat_1('#skF_4',A_152) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_28])).

tff(c_760,plain,(
    ! [A_152] : k9_relat_1('#skF_4',A_152) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_582,c_755])).

tff(c_854,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_relset_1(A_178,B_179,C_180,D_181) = k9_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_857,plain,(
    ! [A_178,B_179,D_181] : k7_relset_1(A_178,B_179,'#skF_4',D_181) = k9_relat_1('#skF_4',D_181) ),
    inference(resolution,[status(thm)],[c_581,c_854])).

tff(c_862,plain,(
    ! [A_178,B_179,D_181] : k7_relset_1(A_178,B_179,'#skF_4',D_181) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_857])).

tff(c_864,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_50])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.48  
% 3.08/1.48  %Foreground sorts:
% 3.08/1.48  
% 3.08/1.48  
% 3.08/1.48  %Background operators:
% 3.08/1.48  
% 3.08/1.48  
% 3.08/1.48  %Foreground operators:
% 3.08/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.08/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.08/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.08/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.08/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.48  
% 3.08/1.49  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.08/1.49  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.08/1.49  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.08/1.49  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.08/1.49  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.49  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.08/1.49  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.08/1.49  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.08/1.49  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/1.49  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.08/1.49  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.49  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.08/1.49  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.08/1.49  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.08/1.49  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.08/1.49  tff(c_106, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.08/1.49  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_106])).
% 3.08/1.49  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.49  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.08/1.49  tff(c_38, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.08/1.49  tff(c_127, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_119, c_38])).
% 3.08/1.49  tff(c_143, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127])).
% 3.08/1.49  tff(c_216, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.49  tff(c_229, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_216])).
% 3.08/1.49  tff(c_301, plain, (![B_80, A_81]: (r1_tarski(k1_relat_1(B_80), A_81) | ~v4_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.49  tff(c_8, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.49  tff(c_381, plain, (![B_105, B_106]: (k1_tarski(B_105)=k1_relat_1(B_106) | k1_relat_1(B_106)=k1_xboole_0 | ~v4_relat_1(B_106, k1_tarski(B_105)) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_301, c_8])).
% 3.08/1.49  tff(c_384, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_229, c_381])).
% 3.08/1.49  tff(c_391, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_384])).
% 3.08/1.49  tff(c_392, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_143, c_391])).
% 3.08/1.49  tff(c_40, plain, (![B_25, A_24]: (k1_tarski(k1_funct_1(B_25, A_24))=k2_relat_1(B_25) | k1_tarski(A_24)!=k1_relat_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.49  tff(c_428, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_54])).
% 3.08/1.49  tff(c_48, plain, (![A_32, B_33, C_34, D_35]: (k7_relset_1(A_32, B_33, C_34, D_35)=k9_relat_1(C_34, D_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.08/1.49  tff(c_531, plain, (![D_35]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_35)=k9_relat_1('#skF_4', D_35))), inference(resolution, [status(thm)], [c_428, c_48])).
% 3.08/1.49  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.08/1.49  tff(c_426, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_50])).
% 3.08/1.49  tff(c_547, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_426])).
% 3.08/1.49  tff(c_559, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_547])).
% 3.08/1.49  tff(c_561, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_58, c_392, c_559])).
% 3.08/1.49  tff(c_564, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_561])).
% 3.08/1.49  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_564])).
% 3.08/1.49  tff(c_569, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_127])).
% 3.08/1.49  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.49  tff(c_79, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.49  tff(c_87, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_14, c_79])).
% 3.08/1.49  tff(c_580, plain, (![A_9]: (r1_tarski('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_87])).
% 3.08/1.49  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.49  tff(c_582, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_569, c_569, c_32])).
% 3.08/1.49  tff(c_581, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_14])).
% 3.08/1.49  tff(c_722, plain, (![C_146, A_147, B_148]: (v4_relat_1(C_146, A_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.49  tff(c_733, plain, (![A_149]: (v4_relat_1('#skF_4', A_149))), inference(resolution, [status(thm)], [c_581, c_722])).
% 3.08/1.49  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.08/1.49  tff(c_736, plain, (![A_149]: (k7_relat_1('#skF_4', A_149)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_733, c_30])).
% 3.08/1.49  tff(c_750, plain, (![A_152]: (k7_relat_1('#skF_4', A_152)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_736])).
% 3.08/1.49  tff(c_28, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.08/1.49  tff(c_755, plain, (![A_152]: (k9_relat_1('#skF_4', A_152)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_750, c_28])).
% 3.08/1.49  tff(c_760, plain, (![A_152]: (k9_relat_1('#skF_4', A_152)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_582, c_755])).
% 3.08/1.49  tff(c_854, plain, (![A_178, B_179, C_180, D_181]: (k7_relset_1(A_178, B_179, C_180, D_181)=k9_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.08/1.49  tff(c_857, plain, (![A_178, B_179, D_181]: (k7_relset_1(A_178, B_179, '#skF_4', D_181)=k9_relat_1('#skF_4', D_181))), inference(resolution, [status(thm)], [c_581, c_854])).
% 3.08/1.49  tff(c_862, plain, (![A_178, B_179, D_181]: (k7_relset_1(A_178, B_179, '#skF_4', D_181)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_857])).
% 3.08/1.49  tff(c_864, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_862, c_50])).
% 3.08/1.49  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_864])).
% 3.08/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  Inference rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Ref     : 0
% 3.08/1.49  #Sup     : 161
% 3.08/1.49  #Fact    : 0
% 3.08/1.49  #Define  : 0
% 3.08/1.49  #Split   : 3
% 3.08/1.49  #Chain   : 0
% 3.08/1.49  #Close   : 0
% 3.08/1.49  
% 3.08/1.49  Ordering : KBO
% 3.08/1.49  
% 3.08/1.49  Simplification rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Subsume      : 1
% 3.08/1.49  #Demod        : 143
% 3.08/1.49  #Tautology    : 105
% 3.08/1.49  #SimpNegUnit  : 1
% 3.08/1.49  #BackRed      : 20
% 3.08/1.49  
% 3.08/1.49  #Partial instantiations: 0
% 3.08/1.49  #Strategies tried      : 1
% 3.08/1.49  
% 3.08/1.49  Timing (in seconds)
% 3.08/1.49  ----------------------
% 3.08/1.49  Preprocessing        : 0.35
% 3.08/1.49  Parsing              : 0.18
% 3.08/1.49  CNF conversion       : 0.02
% 3.08/1.49  Main loop            : 0.37
% 3.08/1.49  Inferencing          : 0.14
% 3.08/1.49  Reduction            : 0.12
% 3.08/1.49  Demodulation         : 0.09
% 3.08/1.49  BG Simplification    : 0.02
% 3.08/1.49  Subsumption          : 0.05
% 3.08/1.50  Abstraction          : 0.02
% 3.08/1.50  MUC search           : 0.00
% 3.08/1.50  Cooper               : 0.00
% 3.08/1.50  Total                : 0.75
% 3.08/1.50  Index Insertion      : 0.00
% 3.08/1.50  Index Deletion       : 0.00
% 3.08/1.50  Index Matching       : 0.00
% 3.08/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
