%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   60 (  74 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 111 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_43])).

tff(c_16,plain,(
    ! [A_17,B_18] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_17,B_18)),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_31,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_relat_1(k2_zfmisc_1(A_17,B_18)),A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_16,c_31])).

tff(c_60,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(k1_relat_1(k2_zfmisc_1(A_54,B_55)),C_56)
      | ~ r1_tarski(A_54,C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_60])).

tff(c_10,plain,(
    ! [B_14,A_13] :
      ( v4_relat_1(B_14,A_13)
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109,plain,(
    ! [A_54,B_55,C_56] :
      ( v4_relat_1(k2_zfmisc_1(A_54,B_55),C_56)
      | ~ v1_relat_1(k2_zfmisc_1(A_54,B_55))
      | ~ r1_tarski(A_54,C_56) ) ),
    inference(resolution,[status(thm)],[c_106,c_10])).

tff(c_139,plain,(
    ! [A_61,B_62,C_63] :
      ( v4_relat_1(k2_zfmisc_1(A_61,B_62),C_63)
      | ~ r1_tarski(A_61,C_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_117,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(B_59))
      | ~ v4_relat_1(B_59,A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_119,plain,(
    ! [A_58] :
      ( v4_relat_1('#skF_4',A_58)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_2','#skF_1'),A_58)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_122,plain,(
    ! [A_58] :
      ( v4_relat_1('#skF_4',A_58)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_2','#skF_1'),A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_151,plain,(
    ! [C_64] :
      ( v4_relat_1('#skF_4',C_64)
      | ~ r1_tarski('#skF_2',C_64) ) ),
    inference(resolution,[status(thm)],[c_139,c_122])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,(
    ! [C_64] :
      ( k7_relat_1('#skF_4',C_64) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',C_64) ) ),
    inference(resolution,[status(thm)],[c_151,c_18])).

tff(c_162,plain,(
    ! [C_69] :
      ( k7_relat_1('#skF_4',C_69) = '#skF_4'
      | ~ r1_tarski('#skF_2',C_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_154])).

tff(c_170,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_158,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k5_relset_1(A_65,B_66,C_67,D_68) = k7_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,(
    ! [D_68] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_68) = k7_relat_1('#skF_4',D_68) ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_176,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_24])).

tff(c_177,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_176])).

tff(c_280,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( r2_relset_1(A_83,B_84,C_85,C_85)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_330,plain,(
    ! [C_89] :
      ( r2_relset_1('#skF_2','#skF_1',C_89,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_280])).

tff(c_332,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_330])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:25:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.27  %$ r2_relset_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.27  
% 2.15/1.27  %Foreground sorts:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Background operators:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Foreground operators:
% 2.15/1.27  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.15/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.27  
% 2.15/1.29  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.15/1.29  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.15/1.29  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.15/1.29  tff(f_59, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.15/1.29  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.15/1.29  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.15/1.29  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.15/1.29  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_relat_1)).
% 2.15/1.29  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.15/1.29  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.15/1.29  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.15/1.29  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.15/1.29  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.29  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.15/1.29  tff(c_40, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.29  tff(c_43, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.15/1.29  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_43])).
% 2.15/1.29  tff(c_16, plain, (![A_17, B_18]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_17, B_18)), A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.29  tff(c_31, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.29  tff(c_38, plain, (![A_17, B_18]: (k2_xboole_0(k1_relat_1(k2_zfmisc_1(A_17, B_18)), A_17)=A_17)), inference(resolution, [status(thm)], [c_16, c_31])).
% 2.15/1.29  tff(c_60, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.29  tff(c_106, plain, (![A_54, B_55, C_56]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_54, B_55)), C_56) | ~r1_tarski(A_54, C_56))), inference(superposition, [status(thm), theory('equality')], [c_38, c_60])).
% 2.15/1.29  tff(c_10, plain, (![B_14, A_13]: (v4_relat_1(B_14, A_13) | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.29  tff(c_109, plain, (![A_54, B_55, C_56]: (v4_relat_1(k2_zfmisc_1(A_54, B_55), C_56) | ~v1_relat_1(k2_zfmisc_1(A_54, B_55)) | ~r1_tarski(A_54, C_56))), inference(resolution, [status(thm)], [c_106, c_10])).
% 2.15/1.29  tff(c_139, plain, (![A_61, B_62, C_63]: (v4_relat_1(k2_zfmisc_1(A_61, B_62), C_63) | ~r1_tarski(A_61, C_63))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_109])).
% 2.15/1.29  tff(c_117, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(B_59)) | ~v4_relat_1(B_59, A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_119, plain, (![A_58]: (v4_relat_1('#skF_4', A_58) | ~v4_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'), A_58) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_117])).
% 2.15/1.29  tff(c_122, plain, (![A_58]: (v4_relat_1('#skF_4', A_58) | ~v4_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'), A_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_119])).
% 2.15/1.29  tff(c_151, plain, (![C_64]: (v4_relat_1('#skF_4', C_64) | ~r1_tarski('#skF_2', C_64))), inference(resolution, [status(thm)], [c_139, c_122])).
% 2.15/1.29  tff(c_18, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.29  tff(c_154, plain, (![C_64]: (k7_relat_1('#skF_4', C_64)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', C_64))), inference(resolution, [status(thm)], [c_151, c_18])).
% 2.15/1.29  tff(c_162, plain, (![C_69]: (k7_relat_1('#skF_4', C_69)='#skF_4' | ~r1_tarski('#skF_2', C_69))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_154])).
% 2.15/1.29  tff(c_170, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_162])).
% 2.15/1.29  tff(c_158, plain, (![A_65, B_66, C_67, D_68]: (k5_relset_1(A_65, B_66, C_67, D_68)=k7_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.29  tff(c_161, plain, (![D_68]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_68)=k7_relat_1('#skF_4', D_68))), inference(resolution, [status(thm)], [c_28, c_158])).
% 2.15/1.29  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.15/1.29  tff(c_176, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_24])).
% 2.15/1.29  tff(c_177, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_176])).
% 2.15/1.29  tff(c_280, plain, (![A_83, B_84, C_85, D_86]: (r2_relset_1(A_83, B_84, C_85, C_85) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.15/1.29  tff(c_330, plain, (![C_89]: (r2_relset_1('#skF_2', '#skF_1', C_89, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_28, c_280])).
% 2.15/1.29  tff(c_332, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_330])).
% 2.15/1.29  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_332])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 64
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 0
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 0
% 2.15/1.29  #Demod        : 22
% 2.15/1.29  #Tautology    : 28
% 2.15/1.29  #SimpNegUnit  : 1
% 2.15/1.29  #BackRed      : 1
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.30
% 2.15/1.29  Parsing              : 0.17
% 2.15/1.29  CNF conversion       : 0.02
% 2.15/1.29  Main loop            : 0.21
% 2.15/1.29  Inferencing          : 0.09
% 2.15/1.29  Reduction            : 0.06
% 2.15/1.29  Demodulation         : 0.05
% 2.15/1.29  BG Simplification    : 0.01
% 2.15/1.29  Subsumption          : 0.03
% 2.15/1.29  Abstraction          : 0.01
% 2.15/1.29  MUC search           : 0.00
% 2.15/1.29  Cooper               : 0.00
% 2.15/1.29  Total                : 0.54
% 2.15/1.29  Index Insertion      : 0.00
% 2.15/1.29  Index Deletion       : 0.00
% 2.15/1.29  Index Matching       : 0.00
% 2.15/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
