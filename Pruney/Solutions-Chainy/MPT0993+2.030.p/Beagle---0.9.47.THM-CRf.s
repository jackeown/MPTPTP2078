%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 169 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_91,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_128,plain,(
    ! [B_57,A_58] :
      ( k7_relat_1(B_57,A_58) = B_57
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_128])).

tff(c_138,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_134])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_67,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_4')
      | ~ r1_tarski(A_45,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_82,plain,(
    ! [B_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,'#skF_2')),'#skF_4')
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_142,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_82])).

tff(c_149,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_142])).

tff(c_226,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_232,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_226])).

tff(c_248,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_306,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_311,plain,(
    ! [D_83] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_83) = k7_relat_1('#skF_5',D_83)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_306])).

tff(c_315,plain,(
    ! [D_83] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_83) = k7_relat_1('#skF_5',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_311])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_316,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_26])).

tff(c_317,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_316])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [D_28,A_22,B_23,C_24] :
      ( k1_funct_1(D_28,'#skF_1'(A_22,B_23,C_24,D_28)) != k1_funct_1(C_24,'#skF_1'(A_22,B_23,C_24,D_28))
      | r2_relset_1(A_22,B_23,C_24,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(D_28,A_22,B_23)
      | ~ v1_funct_1(D_28)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_763,plain,(
    ! [A_160,B_161,C_162] :
      ( r2_relset_1(A_160,B_161,C_162,C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_2(C_162,A_160,B_161)
      | ~ v1_funct_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_2(C_162,A_160,B_161)
      | ~ v1_funct_1(C_162) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22])).

tff(c_768,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_763])).

tff(c_772,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_768])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.56  
% 3.28/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.57  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.28/1.57  
% 3.28/1.57  %Foreground sorts:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Background operators:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Foreground operators:
% 3.28/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.57  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.28/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.57  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.28/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.28/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.57  
% 3.28/1.58  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 3.28/1.58  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.58  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.58  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.28/1.58  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.28/1.58  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.28/1.58  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.28/1.58  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.28/1.58  tff(f_87, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 3.28/1.58  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.28/1.58  tff(c_45, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.58  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_45])).
% 3.28/1.58  tff(c_91, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.28/1.58  tff(c_100, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_91])).
% 3.28/1.58  tff(c_128, plain, (![B_57, A_58]: (k7_relat_1(B_57, A_58)=B_57 | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.58  tff(c_134, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_128])).
% 3.28/1.58  tff(c_138, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_134])).
% 3.28/1.58  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.58  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.28/1.58  tff(c_67, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.58  tff(c_77, plain, (![A_45]: (r1_tarski(A_45, '#skF_4') | ~r1_tarski(A_45, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_67])).
% 3.28/1.58  tff(c_82, plain, (![B_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, '#skF_2')), '#skF_4') | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_10, c_77])).
% 3.28/1.58  tff(c_142, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_82])).
% 3.28/1.58  tff(c_149, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_142])).
% 3.28/1.58  tff(c_226, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.58  tff(c_232, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_149, c_226])).
% 3.28/1.58  tff(c_248, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_232])).
% 3.28/1.58  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.28/1.58  tff(c_306, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.58  tff(c_311, plain, (![D_83]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_83)=k7_relat_1('#skF_5', D_83) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_306])).
% 3.28/1.58  tff(c_315, plain, (![D_83]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_83)=k7_relat_1('#skF_5', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_311])).
% 3.28/1.58  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.28/1.58  tff(c_316, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_26])).
% 3.28/1.58  tff(c_317, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_316])).
% 3.28/1.58  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.28/1.58  tff(c_22, plain, (![D_28, A_22, B_23, C_24]: (k1_funct_1(D_28, '#skF_1'(A_22, B_23, C_24, D_28))!=k1_funct_1(C_24, '#skF_1'(A_22, B_23, C_24, D_28)) | r2_relset_1(A_22, B_23, C_24, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(D_28, A_22, B_23) | ~v1_funct_1(D_28) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.28/1.58  tff(c_763, plain, (![A_160, B_161, C_162]: (r2_relset_1(A_160, B_161, C_162, C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_2(C_162, A_160, B_161) | ~v1_funct_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_2(C_162, A_160, B_161) | ~v1_funct_1(C_162))), inference(reflexivity, [status(thm), theory('equality')], [c_22])).
% 3.28/1.58  tff(c_768, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_763])).
% 3.28/1.58  tff(c_772, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_768])).
% 3.28/1.58  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_772])).
% 3.28/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  Inference rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Ref     : 1
% 3.28/1.59  #Sup     : 162
% 3.28/1.59  #Fact    : 0
% 3.28/1.59  #Define  : 0
% 3.28/1.59  #Split   : 2
% 3.28/1.59  #Chain   : 0
% 3.28/1.59  #Close   : 0
% 3.28/1.59  
% 3.28/1.59  Ordering : KBO
% 3.28/1.59  
% 3.28/1.59  Simplification rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Subsume      : 36
% 3.28/1.59  #Demod        : 55
% 3.28/1.59  #Tautology    : 20
% 3.28/1.59  #SimpNegUnit  : 2
% 3.28/1.59  #BackRed      : 1
% 3.28/1.59  
% 3.28/1.59  #Partial instantiations: 0
% 3.28/1.59  #Strategies tried      : 1
% 3.28/1.59  
% 3.28/1.59  Timing (in seconds)
% 3.28/1.59  ----------------------
% 3.28/1.59  Preprocessing        : 0.34
% 3.28/1.59  Parsing              : 0.19
% 3.28/1.59  CNF conversion       : 0.02
% 3.28/1.59  Main loop            : 0.44
% 3.28/1.59  Inferencing          : 0.18
% 3.28/1.59  Reduction            : 0.11
% 3.28/1.59  Demodulation         : 0.08
% 3.28/1.59  BG Simplification    : 0.02
% 3.28/1.59  Subsumption          : 0.09
% 3.28/1.59  Abstraction          : 0.02
% 3.28/1.59  MUC search           : 0.00
% 3.28/1.59  Cooper               : 0.00
% 3.28/1.59  Total                : 0.82
% 3.28/1.59  Index Insertion      : 0.00
% 3.28/1.59  Index Deletion       : 0.00
% 3.28/1.59  Index Matching       : 0.00
% 3.28/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
