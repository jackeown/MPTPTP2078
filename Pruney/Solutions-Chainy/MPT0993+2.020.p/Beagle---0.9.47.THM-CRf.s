%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:45 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 161 expanded)
%              Number of equality atoms :   10 (  10 expanded)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_79,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_31,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_43,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_43])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_63,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,'#skF_4')
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_76,plain,(
    ! [B_45] :
      ( r1_tarski(k1_relat_1(B_45),'#skF_4')
      | ~ v4_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [B_46] :
      ( v4_relat_1(B_46,'#skF_4')
      | ~ v4_relat_1(B_46,'#skF_2')
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_87,plain,
    ( v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_47,c_84])).

tff(c_90,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_87])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_8])).

tff(c_96,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_93])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_124,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k2_partfun1(A_56,B_57,C_58,D_59) = k7_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,(
    ! [D_59] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_59) = k7_relat_1('#skF_5',D_59)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_129,plain,(
    ! [D_59] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_59) = k7_relat_1('#skF_5',D_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_126])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_130,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_130])).

tff(c_28,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    ! [D_24,A_18,B_19,C_20] :
      ( k1_funct_1(D_24,'#skF_1'(A_18,B_19,C_20,D_24)) != k1_funct_1(C_20,'#skF_1'(A_18,B_19,C_20,D_24))
      | r2_relset_1(A_18,B_19,C_20,D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(D_24,A_18,B_19)
      | ~ v1_funct_1(D_24)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_161,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_relset_1(A_73,B_74,C_75,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_2(C_75,A_73,B_74)
      | ~ v1_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_2(C_75,A_73,B_74)
      | ~ v1_funct_1(C_75) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18])).

tff(c_163,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_161])).

tff(c_166,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_163])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:58:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.39  
% 2.30/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.39  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.30/1.39  
% 2.30/1.39  %Foreground sorts:
% 2.30/1.39  
% 2.30/1.39  
% 2.30/1.39  %Background operators:
% 2.30/1.39  
% 2.30/1.39  
% 2.30/1.39  %Foreground operators:
% 2.30/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.39  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.30/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.30/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.30/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.30/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.30/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.30/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.30/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.39  
% 2.30/1.41  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.30/1.41  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.30/1.41  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.30/1.41  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.30/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.30/1.41  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.30/1.41  tff(f_59, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.30/1.41  tff(f_79, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 2.30/1.41  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.30/1.41  tff(c_31, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.41  tff(c_35, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.30/1.41  tff(c_43, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.41  tff(c_47, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_43])).
% 2.30/1.41  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.41  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.30/1.41  tff(c_63, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.41  tff(c_70, plain, (![A_44]: (r1_tarski(A_44, '#skF_4') | ~r1_tarski(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_63])).
% 2.30/1.41  tff(c_76, plain, (![B_45]: (r1_tarski(k1_relat_1(B_45), '#skF_4') | ~v4_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_6, c_70])).
% 2.30/1.41  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.41  tff(c_84, plain, (![B_46]: (v4_relat_1(B_46, '#skF_4') | ~v4_relat_1(B_46, '#skF_2') | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_76, c_4])).
% 2.30/1.41  tff(c_87, plain, (v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_47, c_84])).
% 2.30/1.41  tff(c_90, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_87])).
% 2.30/1.41  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.41  tff(c_93, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_8])).
% 2.30/1.41  tff(c_96, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_93])).
% 2.30/1.41  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.30/1.41  tff(c_124, plain, (![A_56, B_57, C_58, D_59]: (k2_partfun1(A_56, B_57, C_58, D_59)=k7_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.30/1.41  tff(c_126, plain, (![D_59]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_59)=k7_relat_1('#skF_5', D_59) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_124])).
% 2.30/1.41  tff(c_129, plain, (![D_59]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_59)=k7_relat_1('#skF_5', D_59))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_126])).
% 2.30/1.41  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.30/1.41  tff(c_130, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_22])).
% 2.30/1.41  tff(c_131, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_130])).
% 2.30/1.41  tff(c_28, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.30/1.41  tff(c_18, plain, (![D_24, A_18, B_19, C_20]: (k1_funct_1(D_24, '#skF_1'(A_18, B_19, C_20, D_24))!=k1_funct_1(C_20, '#skF_1'(A_18, B_19, C_20, D_24)) | r2_relset_1(A_18, B_19, C_20, D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(D_24, A_18, B_19) | ~v1_funct_1(D_24) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.30/1.41  tff(c_161, plain, (![A_73, B_74, C_75]: (r2_relset_1(A_73, B_74, C_75, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_2(C_75, A_73, B_74) | ~v1_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_2(C_75, A_73, B_74) | ~v1_funct_1(C_75))), inference(reflexivity, [status(thm), theory('equality')], [c_18])).
% 2.30/1.41  tff(c_163, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_161])).
% 2.30/1.41  tff(c_166, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_163])).
% 2.30/1.41  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_166])).
% 2.30/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.41  
% 2.30/1.41  Inference rules
% 2.30/1.41  ----------------------
% 2.30/1.41  #Ref     : 1
% 2.30/1.41  #Sup     : 26
% 2.30/1.41  #Fact    : 0
% 2.30/1.41  #Define  : 0
% 2.30/1.41  #Split   : 0
% 2.30/1.41  #Chain   : 0
% 2.30/1.41  #Close   : 0
% 2.30/1.41  
% 2.30/1.41  Ordering : KBO
% 2.30/1.41  
% 2.30/1.41  Simplification rules
% 2.30/1.41  ----------------------
% 2.30/1.41  #Subsume      : 0
% 2.30/1.41  #Demod        : 15
% 2.30/1.41  #Tautology    : 7
% 2.30/1.41  #SimpNegUnit  : 2
% 2.30/1.41  #BackRed      : 1
% 2.30/1.41  
% 2.30/1.41  #Partial instantiations: 0
% 2.30/1.41  #Strategies tried      : 1
% 2.30/1.41  
% 2.30/1.41  Timing (in seconds)
% 2.30/1.41  ----------------------
% 2.30/1.41  Preprocessing        : 0.36
% 2.30/1.41  Parsing              : 0.18
% 2.30/1.41  CNF conversion       : 0.03
% 2.30/1.41  Main loop            : 0.22
% 2.30/1.41  Inferencing          : 0.09
% 2.30/1.41  Reduction            : 0.06
% 2.30/1.41  Demodulation         : 0.04
% 2.30/1.41  BG Simplification    : 0.02
% 2.30/1.41  Subsumption          : 0.04
% 2.30/1.41  Abstraction          : 0.02
% 2.30/1.41  MUC search           : 0.00
% 2.30/1.41  Cooper               : 0.00
% 2.30/1.41  Total                : 0.62
% 2.30/1.41  Index Insertion      : 0.00
% 2.30/1.41  Index Deletion       : 0.00
% 2.30/1.41  Index Matching       : 0.00
% 2.30/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
