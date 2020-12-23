%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 139 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [B_49,C_47,A_48,E_51,D_50] :
      ( m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(B_49,D_50)))
      | ~ r1_tarski(C_47,D_50)
      | ~ r1_tarski(A_48,B_49)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_48,C_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    ! [E_52,B_53,B_54,A_55] :
      ( m1_subset_1(E_52,k1_zfmisc_1(k2_zfmisc_1(B_53,B_54)))
      | ~ r1_tarski(A_55,B_53)
      | ~ m1_subset_1(E_52,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_102,plain,(
    ! [E_56,B_57] :
      ( m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_57)))
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_57))) ) ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_106,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_14,plain,(
    ! [C_10,A_8,B_9] :
      ( v4_relat_1(C_10,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_14])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_131,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_128])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k2_partfun1(A_42,B_43,C_44,D_45) = k7_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [D_45] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_45) = k7_relat_1('#skF_5',D_45)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_72])).

tff(c_77,plain,(
    ! [D_45] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_45) = k7_relat_1('#skF_5',D_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_78,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_24])).

tff(c_143,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78])).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [D_26,A_20,B_21,C_22] :
      ( k1_funct_1(D_26,'#skF_1'(A_20,B_21,C_22,D_26)) != k1_funct_1(C_22,'#skF_1'(A_20,B_21,C_22,D_26))
      | r2_relset_1(A_20,B_21,C_22,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_26,A_20,B_21)
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_179,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_relset_1(A_74,B_75,C_76,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20])).

tff(c_183,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_179])).

tff(c_189,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_183])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.16/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.16/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.16/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.29  
% 2.16/1.30  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.16/1.30  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.16/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.30  tff(f_55, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.16/1.30  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.16/1.30  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.16/1.30  tff(f_61, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.16/1.30  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 2.16/1.30  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.30  tff(c_46, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.30  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.16/1.30  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.30  tff(c_88, plain, (![B_49, C_47, A_48, E_51, D_50]: (m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(B_49, D_50))) | ~r1_tarski(C_47, D_50) | ~r1_tarski(A_48, B_49) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_48, C_47))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.30  tff(c_95, plain, (![E_52, B_53, B_54, A_55]: (m1_subset_1(E_52, k1_zfmisc_1(k2_zfmisc_1(B_53, B_54))) | ~r1_tarski(A_55, B_53) | ~m1_subset_1(E_52, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(resolution, [status(thm)], [c_6, c_88])).
% 2.16/1.30  tff(c_102, plain, (![E_56, B_57]: (m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_57))) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_57))))), inference(resolution, [status(thm)], [c_26, c_95])).
% 2.16/1.30  tff(c_106, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_28, c_102])).
% 2.16/1.30  tff(c_14, plain, (![C_10, A_8, B_9]: (v4_relat_1(C_10, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.30  tff(c_123, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_14])).
% 2.16/1.30  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.30  tff(c_128, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_123, c_8])).
% 2.16/1.30  tff(c_131, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_128])).
% 2.16/1.30  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.30  tff(c_72, plain, (![A_42, B_43, C_44, D_45]: (k2_partfun1(A_42, B_43, C_44, D_45)=k7_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.30  tff(c_74, plain, (![D_45]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_45)=k7_relat_1('#skF_5', D_45) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_72])).
% 2.16/1.30  tff(c_77, plain, (![D_45]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_45)=k7_relat_1('#skF_5', D_45))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 2.16/1.30  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.30  tff(c_78, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_24])).
% 2.16/1.30  tff(c_143, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78])).
% 2.16/1.30  tff(c_30, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.30  tff(c_20, plain, (![D_26, A_20, B_21, C_22]: (k1_funct_1(D_26, '#skF_1'(A_20, B_21, C_22, D_26))!=k1_funct_1(C_22, '#skF_1'(A_20, B_21, C_22, D_26)) | r2_relset_1(A_20, B_21, C_22, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_26, A_20, B_21) | ~v1_funct_1(D_26) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.30  tff(c_179, plain, (![A_74, B_75, C_76]: (r2_relset_1(A_74, B_75, C_76, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76))), inference(reflexivity, [status(thm), theory('equality')], [c_20])).
% 2.16/1.30  tff(c_183, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_179])).
% 2.16/1.30  tff(c_189, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_183])).
% 2.16/1.30  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_189])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 1
% 2.16/1.30  #Sup     : 32
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 2
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 1
% 2.16/1.30  #Demod        : 20
% 2.16/1.30  #Tautology    : 13
% 2.16/1.30  #SimpNegUnit  : 2
% 2.16/1.30  #BackRed      : 2
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.16/1.31  Preprocessing        : 0.32
% 2.16/1.31  Parsing              : 0.17
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.18
% 2.16/1.31  Inferencing          : 0.07
% 2.16/1.31  Reduction            : 0.06
% 2.16/1.31  Demodulation         : 0.04
% 2.16/1.31  BG Simplification    : 0.01
% 2.16/1.31  Subsumption          : 0.03
% 2.16/1.31  Abstraction          : 0.01
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.53
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.31  Index Deletion       : 0.00
% 2.16/1.31  Index Matching       : 0.00
% 2.16/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
