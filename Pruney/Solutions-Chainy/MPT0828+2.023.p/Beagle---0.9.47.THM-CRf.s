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
% DateTime   : Thu Dec  3 10:07:20 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 189 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_34,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_220,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_224,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_220])).

tff(c_111,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_115,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_111])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_116,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_61])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_59,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_67,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_71,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_77,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_74])).

tff(c_30,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_relat_1(A_52),k1_relat_1(B_53))
      | ~ r1_tarski(A_52,B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_12,B_53] :
      ( r1_tarski(A_12,k1_relat_1(B_53))
      | ~ r1_tarski(k6_relat_1(A_12),B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_139])).

tff(c_161,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,k1_relat_1(B_57))
      | ~ r1_tarski(k6_relat_1(A_56),B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_151])).

tff(c_164,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_167,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_164])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_18])).

tff(c_173,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_77,c_170])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_173])).

tff(c_176,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_225,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_176])).

tff(c_16,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_230,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k2_relat_1(A_71),k2_relat_1(B_72))
      | ~ r1_tarski(A_71,B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_233,plain,(
    ! [A_12,B_72] :
      ( r1_tarski(A_12,k2_relat_1(B_72))
      | ~ r1_tarski(k6_relat_1(A_12),B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_230])).

tff(c_241,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,k2_relat_1(B_74))
      | ~ r1_tarski(k6_relat_1(A_73),B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_233])).

tff(c_244,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_241])).

tff(c_247,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_247])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.30  
% 2.20/1.30  %Foreground sorts:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Background operators:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Foreground operators:
% 2.20/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.20/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.20/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.20/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.30  
% 2.20/1.32  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.20/1.32  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.20/1.32  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.20/1.32  tff(f_36, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.20/1.32  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.20/1.32  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.20/1.32  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.20/1.32  tff(f_34, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.20/1.32  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.20/1.32  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.20/1.32  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.20/1.32  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.32  tff(c_220, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.20/1.32  tff(c_224, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_220])).
% 2.20/1.32  tff(c_111, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.32  tff(c_115, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_111])).
% 2.20/1.32  tff(c_28, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.32  tff(c_61, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.20/1.32  tff(c_116, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_61])).
% 2.20/1.32  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.20/1.32  tff(c_53, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.32  tff(c_56, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_53])).
% 2.20/1.32  tff(c_59, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56])).
% 2.20/1.32  tff(c_67, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.32  tff(c_71, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_67])).
% 2.20/1.32  tff(c_8, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.20/1.32  tff(c_74, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_8])).
% 2.20/1.32  tff(c_77, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_74])).
% 2.20/1.32  tff(c_30, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.32  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.20/1.32  tff(c_14, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.32  tff(c_139, plain, (![A_52, B_53]: (r1_tarski(k1_relat_1(A_52), k1_relat_1(B_53)) | ~r1_tarski(A_52, B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.32  tff(c_151, plain, (![A_12, B_53]: (r1_tarski(A_12, k1_relat_1(B_53)) | ~r1_tarski(k6_relat_1(A_12), B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_139])).
% 2.20/1.32  tff(c_161, plain, (![A_56, B_57]: (r1_tarski(A_56, k1_relat_1(B_57)) | ~r1_tarski(k6_relat_1(A_56), B_57) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_151])).
% 2.20/1.32  tff(c_164, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_161])).
% 2.20/1.32  tff(c_167, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_164])).
% 2.20/1.32  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.32  tff(c_170, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_167, c_18])).
% 2.20/1.32  tff(c_173, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_77, c_170])).
% 2.20/1.32  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_173])).
% 2.20/1.32  tff(c_176, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 2.20/1.32  tff(c_225, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_176])).
% 2.20/1.32  tff(c_16, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.32  tff(c_230, plain, (![A_71, B_72]: (r1_tarski(k2_relat_1(A_71), k2_relat_1(B_72)) | ~r1_tarski(A_71, B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.32  tff(c_233, plain, (![A_12, B_72]: (r1_tarski(A_12, k2_relat_1(B_72)) | ~r1_tarski(k6_relat_1(A_12), B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_230])).
% 2.20/1.32  tff(c_241, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_relat_1(B_74)) | ~r1_tarski(k6_relat_1(A_73), B_74) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_233])).
% 2.20/1.32  tff(c_244, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_241])).
% 2.20/1.32  tff(c_247, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_244])).
% 2.20/1.32  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_225, c_247])).
% 2.20/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  Inference rules
% 2.20/1.32  ----------------------
% 2.20/1.32  #Ref     : 0
% 2.20/1.32  #Sup     : 46
% 2.20/1.32  #Fact    : 0
% 2.20/1.32  #Define  : 0
% 2.20/1.32  #Split   : 1
% 2.20/1.32  #Chain   : 0
% 2.20/1.32  #Close   : 0
% 2.20/1.32  
% 2.20/1.32  Ordering : KBO
% 2.20/1.32  
% 2.20/1.32  Simplification rules
% 2.20/1.32  ----------------------
% 2.20/1.32  #Subsume      : 0
% 2.20/1.32  #Demod        : 19
% 2.20/1.32  #Tautology    : 18
% 2.20/1.32  #SimpNegUnit  : 2
% 2.20/1.32  #BackRed      : 2
% 2.20/1.32  
% 2.20/1.32  #Partial instantiations: 0
% 2.20/1.32  #Strategies tried      : 1
% 2.20/1.32  
% 2.20/1.32  Timing (in seconds)
% 2.20/1.32  ----------------------
% 2.20/1.32  Preprocessing        : 0.29
% 2.20/1.32  Parsing              : 0.16
% 2.20/1.32  CNF conversion       : 0.02
% 2.20/1.32  Main loop            : 0.19
% 2.20/1.32  Inferencing          : 0.07
% 2.20/1.32  Reduction            : 0.06
% 2.20/1.32  Demodulation         : 0.04
% 2.20/1.32  BG Simplification    : 0.01
% 2.20/1.32  Subsumption          : 0.02
% 2.20/1.32  Abstraction          : 0.01
% 2.20/1.32  MUC search           : 0.00
% 2.20/1.32  Cooper               : 0.00
% 2.20/1.32  Total                : 0.51
% 2.20/1.32  Index Insertion      : 0.00
% 2.20/1.32  Index Deletion       : 0.00
% 2.20/1.32  Index Matching       : 0.00
% 2.20/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
