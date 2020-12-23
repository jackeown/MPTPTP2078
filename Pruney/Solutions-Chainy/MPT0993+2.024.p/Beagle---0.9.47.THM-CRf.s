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
% DateTime   : Thu Dec  3 10:13:45 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 150 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    ! [A_43,B_44,D_45] :
      ( r2_relset_1(A_43,B_44,D_45,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_32,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_32])).

tff(c_54,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_4])).

tff(c_64,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_61])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_6])).

tff(c_76,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,'#skF_3')
      | ~ r1_tarski(A_36,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_120,plain,(
    ! [D_53,B_54,C_55,A_56] :
      ( m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(B_54,C_55)))
      | ~ r1_tarski(k1_relat_1(D_53),B_54)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_56,C_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,(
    ! [B_57] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_57,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_57) ) ),
    inference(resolution,[status(thm)],[c_26,c_120])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [B_58] :
      ( v4_relat_1('#skF_4',B_58)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_58) ) ),
    inference(resolution,[status(thm)],[c_124,c_12])).

tff(c_152,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_145])).

tff(c_157,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_152])).

tff(c_160,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_4])).

tff(c_163,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_160])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_214,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k2_partfun1(A_61,B_62,C_63,D_64) = k7_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_218,plain,(
    ! [D_64] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_64) = k7_relat_1('#skF_4',D_64)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_214])).

tff(c_224,plain,(
    ! [D_64] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_64) = k7_relat_1('#skF_4',D_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_218])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_225,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_22])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_163,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.26  
% 2.05/1.26  %Foreground sorts:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Background operators:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Foreground operators:
% 2.05/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.05/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.05/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.05/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.26  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.05/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.26  
% 2.19/1.28  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.19/1.28  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.19/1.28  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.19/1.28  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.19/1.28  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.19/1.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.19/1.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.19/1.28  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.19/1.28  tff(f_71, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.19/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.28  tff(c_65, plain, (![A_43, B_44, D_45]: (r2_relset_1(A_43, B_44, D_45, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.28  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.19/1.28  tff(c_32, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.28  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_32])).
% 2.19/1.28  tff(c_54, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.28  tff(c_58, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_54])).
% 2.19/1.28  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.28  tff(c_61, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_4])).
% 2.19/1.28  tff(c_64, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_61])).
% 2.19/1.28  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.28  tff(c_72, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_64, c_6])).
% 2.19/1.28  tff(c_76, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72])).
% 2.19/1.28  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.28  tff(c_43, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.28  tff(c_49, plain, (![A_36]: (r1_tarski(A_36, '#skF_3') | ~r1_tarski(A_36, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_43])).
% 2.19/1.28  tff(c_120, plain, (![D_53, B_54, C_55, A_56]: (m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(B_54, C_55))) | ~r1_tarski(k1_relat_1(D_53), B_54) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_56, C_55))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.28  tff(c_124, plain, (![B_57]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_57, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_57))), inference(resolution, [status(thm)], [c_26, c_120])).
% 2.19/1.28  tff(c_12, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.28  tff(c_145, plain, (![B_58]: (v4_relat_1('#skF_4', B_58) | ~r1_tarski(k1_relat_1('#skF_4'), B_58))), inference(resolution, [status(thm)], [c_124, c_12])).
% 2.19/1.28  tff(c_152, plain, (v4_relat_1('#skF_4', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_49, c_145])).
% 2.19/1.28  tff(c_157, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_152])).
% 2.19/1.28  tff(c_160, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_157, c_4])).
% 2.19/1.28  tff(c_163, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_160])).
% 2.19/1.28  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.28  tff(c_214, plain, (![A_61, B_62, C_63, D_64]: (k2_partfun1(A_61, B_62, C_63, D_64)=k7_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.28  tff(c_218, plain, (![D_64]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_64)=k7_relat_1('#skF_4', D_64) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_214])).
% 2.19/1.28  tff(c_224, plain, (![D_64]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_64)=k7_relat_1('#skF_4', D_64))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_218])).
% 2.19/1.28  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.28  tff(c_225, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_22])).
% 2.19/1.28  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_163, c_225])).
% 2.19/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  Inference rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Ref     : 0
% 2.19/1.28  #Sup     : 43
% 2.19/1.28  #Fact    : 0
% 2.19/1.28  #Define  : 0
% 2.19/1.28  #Split   : 1
% 2.19/1.28  #Chain   : 0
% 2.19/1.28  #Close   : 0
% 2.19/1.28  
% 2.19/1.28  Ordering : KBO
% 2.19/1.28  
% 2.19/1.28  Simplification rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Subsume      : 5
% 2.19/1.28  #Demod        : 21
% 2.19/1.28  #Tautology    : 12
% 2.19/1.28  #SimpNegUnit  : 0
% 2.19/1.28  #BackRed      : 1
% 2.19/1.28  
% 2.19/1.28  #Partial instantiations: 0
% 2.19/1.28  #Strategies tried      : 1
% 2.19/1.28  
% 2.19/1.28  Timing (in seconds)
% 2.19/1.28  ----------------------
% 2.19/1.28  Preprocessing        : 0.29
% 2.19/1.28  Parsing              : 0.16
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.18
% 2.19/1.28  Inferencing          : 0.07
% 2.19/1.28  Reduction            : 0.06
% 2.19/1.28  Demodulation         : 0.04
% 2.19/1.28  BG Simplification    : 0.01
% 2.19/1.28  Subsumption          : 0.03
% 2.19/1.28  Abstraction          : 0.01
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.51
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
