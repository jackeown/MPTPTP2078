%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 110 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_83,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_74,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_12,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_15] : v4_relat_1(k6_relat_1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,(
    ! [C_37,B_38,A_39] :
      ( v4_relat_1(C_37,B_38)
      | ~ v4_relat_1(C_37,A_39)
      | ~ v1_relat_1(C_37)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [A_15,B_38] :
      ( v4_relat_1(k6_relat_1(A_15),B_38)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ r1_tarski(A_15,B_38) ) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_114,plain,(
    ! [A_41,B_42] :
      ( v4_relat_1(k6_relat_1(A_41),B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_101])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119,plain,(
    ! [A_41,B_42] :
      ( k7_relat_1(k6_relat_1(A_41),B_42) = k6_relat_1(A_41)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_114,c_8])).

tff(c_125,plain,(
    ! [A_41,B_42] :
      ( k7_relat_1(k6_relat_1(A_41),B_42) = k6_relat_1(A_41)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_119])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_153,plain,(
    ! [A_45,A_12] :
      ( k1_relat_1(k5_relat_1(A_45,k6_relat_1(A_12))) = k10_relat_1(A_45,A_12)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_144])).

tff(c_158,plain,(
    ! [A_47,A_48] :
      ( k1_relat_1(k5_relat_1(A_47,k6_relat_1(A_48))) = k10_relat_1(A_47,A_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_171,plain,(
    ! [A_48,A_13] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_48),A_13)) = k10_relat_1(k6_relat_1(A_13),A_48)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_176,plain,(
    ! [A_49,A_50] : k1_relat_1(k7_relat_1(k6_relat_1(A_49),A_50)) = k10_relat_1(k6_relat_1(A_50),A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_171])).

tff(c_188,plain,(
    ! [B_42,A_41] :
      ( k10_relat_1(k6_relat_1(B_42),A_41) = k1_relat_1(k6_relat_1(A_41))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_176])).

tff(c_194,plain,(
    ! [B_42,A_41] :
      ( k10_relat_1(k6_relat_1(B_42),A_41) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_188])).

tff(c_26,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_20] : k2_funct_1(k6_relat_1(A_20)) = k6_relat_1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_251,plain,(
    ! [B_57,A_58] :
      ( k9_relat_1(k2_funct_1(B_57),A_58) = k10_relat_1(B_57,A_58)
      | ~ v2_funct_1(B_57)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_260,plain,(
    ! [A_20,A_58] :
      ( k9_relat_1(k6_relat_1(A_20),A_58) = k10_relat_1(k6_relat_1(A_20),A_58)
      | ~ v2_funct_1(k6_relat_1(A_20))
      | ~ v1_funct_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_251])).

tff(c_264,plain,(
    ! [A_20,A_58] : k9_relat_1(k6_relat_1(A_20),A_58) = k10_relat_1(k6_relat_1(A_20),A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_30,c_260])).

tff(c_36,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_277,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_36])).

tff(c_289,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_277])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:29:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.22  
% 2.05/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.22  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.05/1.22  
% 2.05/1.22  %Foreground sorts:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Background operators:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Foreground operators:
% 2.05/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.05/1.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.05/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.05/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.05/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.05/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.22  
% 2.23/1.23  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.23/1.23  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.23/1.23  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.23/1.23  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.23/1.23  tff(f_65, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.23/1.23  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 2.23/1.23  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.23/1.23  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.23/1.23  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.23/1.23  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.23/1.23  tff(f_83, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.23/1.23  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 2.23/1.23  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.23  tff(c_74, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.23  tff(c_82, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.23/1.23  tff(c_12, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.23  tff(c_28, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.23  tff(c_20, plain, (![A_15]: (v4_relat_1(k6_relat_1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.23  tff(c_99, plain, (![C_37, B_38, A_39]: (v4_relat_1(C_37, B_38) | ~v4_relat_1(C_37, A_39) | ~v1_relat_1(C_37) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.23  tff(c_101, plain, (![A_15, B_38]: (v4_relat_1(k6_relat_1(A_15), B_38) | ~v1_relat_1(k6_relat_1(A_15)) | ~r1_tarski(A_15, B_38))), inference(resolution, [status(thm)], [c_20, c_99])).
% 2.23/1.23  tff(c_114, plain, (![A_41, B_42]: (v4_relat_1(k6_relat_1(A_41), B_42) | ~r1_tarski(A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_101])).
% 2.23/1.23  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.23  tff(c_119, plain, (![A_41, B_42]: (k7_relat_1(k6_relat_1(A_41), B_42)=k6_relat_1(A_41) | ~v1_relat_1(k6_relat_1(A_41)) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_114, c_8])).
% 2.23/1.23  tff(c_125, plain, (![A_41, B_42]: (k7_relat_1(k6_relat_1(A_41), B_42)=k6_relat_1(A_41) | ~r1_tarski(A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_119])).
% 2.23/1.23  tff(c_16, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.23  tff(c_144, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.23  tff(c_153, plain, (![A_45, A_12]: (k1_relat_1(k5_relat_1(A_45, k6_relat_1(A_12)))=k10_relat_1(A_45, A_12) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_12, c_144])).
% 2.23/1.23  tff(c_158, plain, (![A_47, A_48]: (k1_relat_1(k5_relat_1(A_47, k6_relat_1(A_48)))=k10_relat_1(A_47, A_48) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153])).
% 2.23/1.23  tff(c_171, plain, (![A_48, A_13]: (k1_relat_1(k7_relat_1(k6_relat_1(A_48), A_13))=k10_relat_1(k6_relat_1(A_13), A_48) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_158])).
% 2.23/1.23  tff(c_176, plain, (![A_49, A_50]: (k1_relat_1(k7_relat_1(k6_relat_1(A_49), A_50))=k10_relat_1(k6_relat_1(A_50), A_49))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_171])).
% 2.23/1.23  tff(c_188, plain, (![B_42, A_41]: (k10_relat_1(k6_relat_1(B_42), A_41)=k1_relat_1(k6_relat_1(A_41)) | ~r1_tarski(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_125, c_176])).
% 2.23/1.23  tff(c_194, plain, (![B_42, A_41]: (k10_relat_1(k6_relat_1(B_42), A_41)=A_41 | ~r1_tarski(A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_188])).
% 2.23/1.23  tff(c_26, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.23  tff(c_30, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.23  tff(c_34, plain, (![A_20]: (k2_funct_1(k6_relat_1(A_20))=k6_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.23  tff(c_251, plain, (![B_57, A_58]: (k9_relat_1(k2_funct_1(B_57), A_58)=k10_relat_1(B_57, A_58) | ~v2_funct_1(B_57) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.23  tff(c_260, plain, (![A_20, A_58]: (k9_relat_1(k6_relat_1(A_20), A_58)=k10_relat_1(k6_relat_1(A_20), A_58) | ~v2_funct_1(k6_relat_1(A_20)) | ~v1_funct_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_251])).
% 2.23/1.23  tff(c_264, plain, (![A_20, A_58]: (k9_relat_1(k6_relat_1(A_20), A_58)=k10_relat_1(k6_relat_1(A_20), A_58))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_30, c_260])).
% 2.23/1.23  tff(c_36, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.23  tff(c_277, plain, (k10_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_36])).
% 2.23/1.23  tff(c_289, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_194, c_277])).
% 2.23/1.23  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_289])).
% 2.23/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.23  
% 2.23/1.23  Inference rules
% 2.23/1.23  ----------------------
% 2.23/1.23  #Ref     : 0
% 2.23/1.23  #Sup     : 51
% 2.23/1.23  #Fact    : 0
% 2.23/1.23  #Define  : 0
% 2.23/1.23  #Split   : 0
% 2.23/1.23  #Chain   : 0
% 2.23/1.23  #Close   : 0
% 2.23/1.23  
% 2.23/1.23  Ordering : KBO
% 2.23/1.23  
% 2.23/1.23  Simplification rules
% 2.23/1.23  ----------------------
% 2.23/1.23  #Subsume      : 0
% 2.23/1.23  #Demod        : 22
% 2.23/1.23  #Tautology    : 33
% 2.23/1.23  #SimpNegUnit  : 0
% 2.23/1.23  #BackRed      : 1
% 2.23/1.23  
% 2.23/1.23  #Partial instantiations: 0
% 2.23/1.23  #Strategies tried      : 1
% 2.23/1.23  
% 2.23/1.23  Timing (in seconds)
% 2.23/1.23  ----------------------
% 2.23/1.24  Preprocessing        : 0.30
% 2.23/1.24  Parsing              : 0.16
% 2.23/1.24  CNF conversion       : 0.02
% 2.23/1.24  Main loop            : 0.17
% 2.23/1.24  Inferencing          : 0.07
% 2.23/1.24  Reduction            : 0.05
% 2.23/1.24  Demodulation         : 0.04
% 2.23/1.24  BG Simplification    : 0.01
% 2.23/1.24  Subsumption          : 0.02
% 2.23/1.24  Abstraction          : 0.01
% 2.23/1.24  MUC search           : 0.00
% 2.23/1.24  Cooper               : 0.00
% 2.23/1.24  Total                : 0.50
% 2.23/1.24  Index Insertion      : 0.00
% 2.23/1.24  Index Deletion       : 0.00
% 2.23/1.24  Index Matching       : 0.00
% 2.23/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
