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
% DateTime   : Thu Dec  3 10:08:40 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   72 (  89 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 110 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_729,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k5_relset_1(A_88,B_89,C_90,D_91) = k7_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_732,plain,(
    ! [D_91] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_91) = k7_relat_1('#skF_4',D_91) ),
    inference(resolution,[status(thm)],[c_38,c_729])).

tff(c_34,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_733,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_34])).

tff(c_252,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_256,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_324,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_328,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_324])).

tff(c_329,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_332,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_328,c_329])).

tff(c_335,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_332])).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_16,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_16])).

tff(c_36,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_97])).

tff(c_149,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_105])).

tff(c_199,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_199])).

tff(c_220,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_208])).

tff(c_188,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_48,A_49)),A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_743,plain,(
    ! [B_93,B_94,C_95] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(B_93,k4_xboole_0(B_94,C_95))),C_95)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_787,plain,(
    ! [B_97] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(B_97,'#skF_3')),'#skF_2')
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_743])).

tff(c_796,plain,
    ( r1_xboole_0(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_787])).

tff(c_801,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_796])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_804,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_801,c_22])).

tff(c_810,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_804])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.75/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.75/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.75/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.38  
% 2.75/1.40  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.75/1.40  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.75/1.40  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.40  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.75/1.40  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.75/1.40  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.75/1.40  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.75/1.40  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.75/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.75/1.40  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.75/1.40  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.75/1.40  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.75/1.40  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.75/1.40  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.40  tff(c_729, plain, (![A_88, B_89, C_90, D_91]: (k5_relset_1(A_88, B_89, C_90, D_91)=k7_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.75/1.40  tff(c_732, plain, (![D_91]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_91)=k7_relat_1('#skF_4', D_91))), inference(resolution, [status(thm)], [c_38, c_729])).
% 2.75/1.40  tff(c_34, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.40  tff(c_733, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_732, c_34])).
% 2.75/1.40  tff(c_252, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.40  tff(c_256, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_252])).
% 2.75/1.40  tff(c_324, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.75/1.40  tff(c_328, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_324])).
% 2.75/1.40  tff(c_329, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.40  tff(c_332, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_328, c_329])).
% 2.75/1.40  tff(c_335, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_332])).
% 2.75/1.40  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.40  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.40  tff(c_82, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.40  tff(c_111, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_14, c_82])).
% 2.75/1.40  tff(c_16, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.40  tff(c_134, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_111, c_16])).
% 2.75/1.40  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.40  tff(c_97, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.40  tff(c_105, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_97])).
% 2.75/1.40  tff(c_149, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_134, c_105])).
% 2.75/1.40  tff(c_199, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.40  tff(c_208, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_149, c_199])).
% 2.75/1.40  tff(c_220, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_208])).
% 2.75/1.40  tff(c_188, plain, (![B_48, A_49]: (r1_tarski(k1_relat_1(k7_relat_1(B_48, A_49)), A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.40  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.40  tff(c_743, plain, (![B_93, B_94, C_95]: (r1_xboole_0(k1_relat_1(k7_relat_1(B_93, k4_xboole_0(B_94, C_95))), C_95) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_188, c_8])).
% 2.75/1.40  tff(c_787, plain, (![B_97]: (r1_xboole_0(k1_relat_1(k7_relat_1(B_97, '#skF_3')), '#skF_2') | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_220, c_743])).
% 2.75/1.40  tff(c_796, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_335, c_787])).
% 2.75/1.40  tff(c_801, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_796])).
% 2.75/1.40  tff(c_22, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.75/1.40  tff(c_804, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_801, c_22])).
% 2.75/1.40  tff(c_810, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_256, c_804])).
% 2.75/1.40  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_733, c_810])).
% 2.75/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  Inference rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Ref     : 0
% 2.75/1.40  #Sup     : 193
% 2.75/1.40  #Fact    : 0
% 2.75/1.40  #Define  : 0
% 2.75/1.40  #Split   : 0
% 2.75/1.40  #Chain   : 0
% 2.75/1.40  #Close   : 0
% 2.75/1.40  
% 2.75/1.40  Ordering : KBO
% 2.75/1.40  
% 2.75/1.40  Simplification rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Subsume      : 21
% 2.75/1.40  #Demod        : 49
% 2.75/1.40  #Tautology    : 104
% 2.75/1.40  #SimpNegUnit  : 1
% 2.75/1.40  #BackRed      : 1
% 2.75/1.40  
% 2.75/1.40  #Partial instantiations: 0
% 2.75/1.40  #Strategies tried      : 1
% 2.75/1.40  
% 2.75/1.40  Timing (in seconds)
% 2.75/1.40  ----------------------
% 2.75/1.40  Preprocessing        : 0.31
% 2.75/1.40  Parsing              : 0.17
% 2.75/1.40  CNF conversion       : 0.02
% 2.75/1.40  Main loop            : 0.33
% 2.75/1.40  Inferencing          : 0.13
% 2.75/1.40  Reduction            : 0.11
% 2.75/1.40  Demodulation         : 0.08
% 2.75/1.40  BG Simplification    : 0.02
% 2.75/1.40  Subsumption          : 0.05
% 2.75/1.40  Abstraction          : 0.02
% 2.75/1.40  MUC search           : 0.00
% 2.75/1.40  Cooper               : 0.00
% 2.75/1.40  Total                : 0.67
% 2.75/1.40  Index Insertion      : 0.00
% 2.75/1.40  Index Deletion       : 0.00
% 2.75/1.40  Index Matching       : 0.00
% 2.75/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
