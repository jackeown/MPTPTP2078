%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:31 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 129 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 220 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( m1_subset_1(A_49,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51)))
      | ~ r1_tarski(A_49,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_188,plain,(
    ! [B_77,A_78,B_79,C_80] :
      ( m1_subset_1(k7_relat_1(B_77,A_78),k1_zfmisc_1(k2_zfmisc_1(B_79,C_80)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_zfmisc_1(B_79,C_80)))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_14,plain,(
    ! [C_14,B_13,A_12] :
      ( v5_relat_1(C_14,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_237,plain,(
    ! [B_85,A_86,C_87,B_88] :
      ( v5_relat_1(k7_relat_1(B_85,A_86),C_87)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(B_88,C_87)))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_245,plain,(
    ! [A_86] :
      ( v5_relat_1(k7_relat_1('#skF_4',A_86),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_237])).

tff(c_251,plain,(
    ! [A_86] : v5_relat_1(k7_relat_1('#skF_4',A_86),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_245])).

tff(c_108,plain,(
    ! [B_62,A_63,B_64,C_65] :
      ( m1_subset_1(k7_relat_1(B_62,A_63),k1_zfmisc_1(k2_zfmisc_1(B_64,C_65)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_zfmisc_1(B_64,C_65)))
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [B_62,A_63,B_64,C_65] :
      ( v1_relat_1(k7_relat_1(B_62,A_63))
      | ~ v1_relat_1(k2_zfmisc_1(B_64,C_65))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_zfmisc_1(B_64,C_65)))
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_157,plain,(
    ! [B_70,A_71,B_72,C_73] :
      ( v1_relat_1(k7_relat_1(B_70,A_71))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_zfmisc_1(B_72,C_73)))
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_165,plain,(
    ! [A_71] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_71))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_171,plain,(
    ! [A_71] : v1_relat_1(k7_relat_1('#skF_4',A_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_77,plain,(
    ! [C_53,A_54,B_55] :
      ( m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ r1_tarski(k2_relat_1(C_53),B_55)
      | ~ r1_tarski(k1_relat_1(C_53),A_54)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k5_relset_1(A_44,B_45,C_46,D_47) = k7_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    ! [D_47] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_47) = k7_relat_1('#skF_4',D_47) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_24])).

tff(c_92,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_77,c_57])).

tff(c_103,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_103])).

tff(c_176,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_175,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_181,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_184,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_187,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_184])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_187])).

tff(c_255,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_259,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_255])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.37  
% 2.37/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.37  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.37  
% 2.37/1.37  %Foreground sorts:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Background operators:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Foreground operators:
% 2.37/1.37  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.37  
% 2.37/1.39  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.39  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.37/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.39  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.37/1.39  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.37/1.39  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 2.37/1.39  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.37/1.39  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.37/1.39  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.37/1.39  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.37/1.39  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.39  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.37/1.39  tff(c_30, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.39  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.37/1.39  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_33])).
% 2.37/1.39  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.37/1.39  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.39  tff(c_67, plain, (![A_49, B_50, C_51, D_52]: (m1_subset_1(A_49, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~r1_tarski(A_49, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.39  tff(c_188, plain, (![B_77, A_78, B_79, C_80]: (m1_subset_1(k7_relat_1(B_77, A_78), k1_zfmisc_1(k2_zfmisc_1(B_79, C_80))) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_zfmisc_1(B_79, C_80))) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_12, c_67])).
% 2.37/1.39  tff(c_14, plain, (![C_14, B_13, A_12]: (v5_relat_1(C_14, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.37/1.39  tff(c_237, plain, (![B_85, A_86, C_87, B_88]: (v5_relat_1(k7_relat_1(B_85, A_86), C_87) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_zfmisc_1(B_88, C_87))) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_188, c_14])).
% 2.37/1.39  tff(c_245, plain, (![A_86]: (v5_relat_1(k7_relat_1('#skF_4', A_86), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_237])).
% 2.37/1.39  tff(c_251, plain, (![A_86]: (v5_relat_1(k7_relat_1('#skF_4', A_86), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_245])).
% 2.37/1.39  tff(c_108, plain, (![B_62, A_63, B_64, C_65]: (m1_subset_1(k7_relat_1(B_62, A_63), k1_zfmisc_1(k2_zfmisc_1(B_64, C_65))) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_zfmisc_1(B_64, C_65))) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_12, c_67])).
% 2.37/1.39  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.39  tff(c_122, plain, (![B_62, A_63, B_64, C_65]: (v1_relat_1(k7_relat_1(B_62, A_63)) | ~v1_relat_1(k2_zfmisc_1(B_64, C_65)) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_zfmisc_1(B_64, C_65))) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_108, c_2])).
% 2.37/1.39  tff(c_157, plain, (![B_70, A_71, B_72, C_73]: (v1_relat_1(k7_relat_1(B_70, A_71)) | ~m1_subset_1(B_70, k1_zfmisc_1(k2_zfmisc_1(B_72, C_73))) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_122])).
% 2.37/1.39  tff(c_165, plain, (![A_71]: (v1_relat_1(k7_relat_1('#skF_4', A_71)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_157])).
% 2.37/1.39  tff(c_171, plain, (![A_71]: (v1_relat_1(k7_relat_1('#skF_4', A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_165])).
% 2.37/1.39  tff(c_77, plain, (![C_53, A_54, B_55]: (m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~r1_tarski(k2_relat_1(C_53), B_55) | ~r1_tarski(k1_relat_1(C_53), A_54) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.39  tff(c_53, plain, (![A_44, B_45, C_46, D_47]: (k5_relset_1(A_44, B_45, C_46, D_47)=k7_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.39  tff(c_56, plain, (![D_47]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_47)=k7_relat_1('#skF_4', D_47))), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.37/1.39  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.37/1.39  tff(c_57, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_24])).
% 2.37/1.39  tff(c_92, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_77, c_57])).
% 2.37/1.39  tff(c_103, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.37/1.39  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_103])).
% 2.37/1.39  tff(c_176, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_92])).
% 2.37/1.39  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.39  tff(c_175, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 2.37/1.39  tff(c_181, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_175])).
% 2.37/1.39  tff(c_184, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_181])).
% 2.37/1.39  tff(c_187, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_184])).
% 2.37/1.39  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_187])).
% 2.37/1.39  tff(c_255, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_175])).
% 2.37/1.39  tff(c_259, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_255])).
% 2.37/1.39  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_259])).
% 2.37/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.39  
% 2.37/1.39  Inference rules
% 2.37/1.39  ----------------------
% 2.37/1.39  #Ref     : 0
% 2.37/1.39  #Sup     : 48
% 2.37/1.39  #Fact    : 0
% 2.37/1.39  #Define  : 0
% 2.37/1.39  #Split   : 4
% 2.37/1.39  #Chain   : 0
% 2.37/1.39  #Close   : 0
% 2.37/1.39  
% 2.37/1.39  Ordering : KBO
% 2.37/1.39  
% 2.37/1.39  Simplification rules
% 2.37/1.39  ----------------------
% 2.37/1.39  #Subsume      : 1
% 2.37/1.39  #Demod        : 17
% 2.37/1.39  #Tautology    : 4
% 2.37/1.39  #SimpNegUnit  : 0
% 2.37/1.39  #BackRed      : 3
% 2.37/1.39  
% 2.37/1.39  #Partial instantiations: 0
% 2.37/1.39  #Strategies tried      : 1
% 2.37/1.39  
% 2.37/1.39  Timing (in seconds)
% 2.37/1.39  ----------------------
% 2.37/1.39  Preprocessing        : 0.28
% 2.37/1.39  Parsing              : 0.15
% 2.37/1.39  CNF conversion       : 0.02
% 2.37/1.39  Main loop            : 0.27
% 2.37/1.39  Inferencing          : 0.11
% 2.37/1.40  Reduction            : 0.07
% 2.37/1.40  Demodulation         : 0.05
% 2.37/1.40  BG Simplification    : 0.02
% 2.37/1.40  Subsumption          : 0.04
% 2.37/1.40  Abstraction          : 0.02
% 2.37/1.40  MUC search           : 0.00
% 2.37/1.40  Cooper               : 0.00
% 2.37/1.40  Total                : 0.59
% 2.37/1.40  Index Insertion      : 0.00
% 2.37/1.40  Index Deletion       : 0.00
% 2.37/1.40  Index Matching       : 0.00
% 2.37/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
