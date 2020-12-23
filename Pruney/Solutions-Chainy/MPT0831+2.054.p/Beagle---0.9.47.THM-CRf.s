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
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   68 (  99 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 161 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_67,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_63])).

tff(c_131,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_140,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_131])).

tff(c_236,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k1_relset_1(A_75,B_76,C_77),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_249,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_236])).

tff(c_254,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_249])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_262,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_254,c_6])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( v4_relat_1(B_12,A_11)
      | ~ r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_267,plain,
    ( v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_12])).

tff(c_277,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_267])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k1_relat_1(B_54),A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [B_56,A_57] :
      ( k2_xboole_0(k1_relat_1(B_56),A_57) = A_57
      | ~ v4_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [B_68,C_69,A_70] :
      ( r1_tarski(k1_relat_1(B_68),C_69)
      | ~ r1_tarski(A_70,C_69)
      | ~ v4_relat_1(B_68,A_70)
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_176,plain,(
    ! [B_71] :
      ( r1_tarski(k1_relat_1(B_71),'#skF_3')
      | ~ v4_relat_1(B_71,'#skF_2')
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_189,plain,(
    ! [B_71] :
      ( v4_relat_1(B_71,'#skF_3')
      | ~ v4_relat_1(B_71,'#skF_2')
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_176,c_12])).

tff(c_282,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_189])).

tff(c_290,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_282])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_302,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_290,c_18])).

tff(c_308,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_302])).

tff(c_318,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k5_relset_1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_329,plain,(
    ! [D_83] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(resolution,[status(thm)],[c_32,c_318])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_349,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_28])).

tff(c_350,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_349])).

tff(c_420,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_relset_1(A_89,B_90,C_91,C_91)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_481,plain,(
    ! [C_95] :
      ( r2_relset_1('#skF_2','#skF_1',C_95,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_420])).

tff(c_489,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_481])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  
% 2.32/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  %$ r2_relset_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.37  
% 2.32/1.37  %Foreground sorts:
% 2.32/1.37  
% 2.32/1.37  
% 2.32/1.37  %Background operators:
% 2.32/1.37  
% 2.32/1.37  
% 2.32/1.37  %Foreground operators:
% 2.32/1.37  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.32/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.32/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.32/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.37  
% 2.59/1.39  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.59/1.39  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.59/1.39  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.59/1.39  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.59/1.39  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.59/1.39  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.59/1.39  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.59/1.39  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.59/1.39  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.59/1.39  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.59/1.39  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.59/1.39  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.59/1.39  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.59/1.39  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.59/1.39  tff(c_57, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.39  tff(c_63, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_57])).
% 2.59/1.39  tff(c_67, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_63])).
% 2.59/1.39  tff(c_131, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.39  tff(c_140, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_131])).
% 2.59/1.39  tff(c_236, plain, (![A_75, B_76, C_77]: (m1_subset_1(k1_relset_1(A_75, B_76, C_77), k1_zfmisc_1(A_75)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.39  tff(c_249, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_236])).
% 2.59/1.39  tff(c_254, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_249])).
% 2.59/1.39  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.39  tff(c_262, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_254, c_6])).
% 2.59/1.39  tff(c_12, plain, (![B_12, A_11]: (v4_relat_1(B_12, A_11) | ~r1_tarski(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.39  tff(c_267, plain, (v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_262, c_12])).
% 2.59/1.39  tff(c_277, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_267])).
% 2.59/1.39  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.59/1.39  tff(c_106, plain, (![B_54, A_55]: (r1_tarski(k1_relat_1(B_54), A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.39  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.39  tff(c_119, plain, (![B_56, A_57]: (k2_xboole_0(k1_relat_1(B_56), A_57)=A_57 | ~v4_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_106, c_4])).
% 2.59/1.39  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.39  tff(c_163, plain, (![B_68, C_69, A_70]: (r1_tarski(k1_relat_1(B_68), C_69) | ~r1_tarski(A_70, C_69) | ~v4_relat_1(B_68, A_70) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_119, c_2])).
% 2.59/1.39  tff(c_176, plain, (![B_71]: (r1_tarski(k1_relat_1(B_71), '#skF_3') | ~v4_relat_1(B_71, '#skF_2') | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_30, c_163])).
% 2.59/1.39  tff(c_189, plain, (![B_71]: (v4_relat_1(B_71, '#skF_3') | ~v4_relat_1(B_71, '#skF_2') | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_176, c_12])).
% 2.59/1.39  tff(c_282, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_277, c_189])).
% 2.59/1.39  tff(c_290, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_282])).
% 2.59/1.39  tff(c_18, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.59/1.39  tff(c_302, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_290, c_18])).
% 2.59/1.39  tff(c_308, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_302])).
% 2.59/1.39  tff(c_318, plain, (![A_80, B_81, C_82, D_83]: (k5_relset_1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.39  tff(c_329, plain, (![D_83]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(resolution, [status(thm)], [c_32, c_318])).
% 2.59/1.39  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.59/1.39  tff(c_349, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_28])).
% 2.59/1.39  tff(c_350, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_349])).
% 2.59/1.39  tff(c_420, plain, (![A_89, B_90, C_91, D_92]: (r2_relset_1(A_89, B_90, C_91, C_91) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.59/1.39  tff(c_481, plain, (![C_95]: (r2_relset_1('#skF_2', '#skF_1', C_95, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_420])).
% 2.59/1.39  tff(c_489, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_481])).
% 2.59/1.39  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_350, c_489])).
% 2.59/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  Inference rules
% 2.59/1.39  ----------------------
% 2.59/1.39  #Ref     : 0
% 2.59/1.39  #Sup     : 102
% 2.59/1.39  #Fact    : 0
% 2.59/1.39  #Define  : 0
% 2.59/1.39  #Split   : 4
% 2.59/1.39  #Chain   : 0
% 2.59/1.39  #Close   : 0
% 2.59/1.39  
% 2.59/1.39  Ordering : KBO
% 2.59/1.39  
% 2.59/1.39  Simplification rules
% 2.59/1.39  ----------------------
% 2.59/1.39  #Subsume      : 4
% 2.59/1.39  #Demod        : 33
% 2.59/1.39  #Tautology    : 36
% 2.59/1.39  #SimpNegUnit  : 1
% 2.59/1.39  #BackRed      : 1
% 2.59/1.39  
% 2.59/1.39  #Partial instantiations: 0
% 2.59/1.39  #Strategies tried      : 1
% 2.59/1.39  
% 2.59/1.39  Timing (in seconds)
% 2.59/1.39  ----------------------
% 2.59/1.39  Preprocessing        : 0.30
% 2.59/1.39  Parsing              : 0.17
% 2.59/1.39  CNF conversion       : 0.02
% 2.59/1.39  Main loop            : 0.27
% 2.59/1.39  Inferencing          : 0.11
% 2.59/1.39  Reduction            : 0.08
% 2.59/1.39  Demodulation         : 0.05
% 2.59/1.39  BG Simplification    : 0.02
% 2.59/1.39  Subsumption          : 0.05
% 2.59/1.39  Abstraction          : 0.02
% 2.59/1.39  MUC search           : 0.00
% 2.59/1.39  Cooper               : 0.00
% 2.59/1.39  Total                : 0.61
% 2.59/1.39  Index Insertion      : 0.00
% 2.59/1.39  Index Deletion       : 0.00
% 2.59/1.39  Index Matching       : 0.00
% 2.59/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
