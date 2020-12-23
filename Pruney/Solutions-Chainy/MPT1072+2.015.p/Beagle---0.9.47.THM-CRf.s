%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 114 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 311 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_88,plain,(
    ! [D_42,C_43,A_44,B_45] :
      ( r2_hidden(k1_funct_1(D_42,C_43),k2_relset_1(A_44,B_45,D_42))
      | k1_xboole_0 = B_45
      | ~ r2_hidden(C_43,A_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_42,A_44,B_45)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( k3_funct_2(A_36,B_37,C_38,D_39) = k1_funct_1(C_38,D_39)
      | ~ m1_subset_1(D_39,A_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [B_37,C_38] :
      ( k3_funct_2('#skF_2',B_37,C_38,'#skF_4') = k1_funct_1(C_38,'#skF_4')
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_37)))
      | ~ v1_funct_2(C_38,'#skF_2',B_37)
      | ~ v1_funct_1(C_38)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_65,plain,(
    ! [B_40,C_41] :
      ( k3_funct_2('#skF_2',B_40,C_41,'#skF_4') = k1_funct_1(C_41,'#skF_4')
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_40)))
      | ~ v1_funct_2(C_41,'#skF_2',B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_58])).

tff(c_68,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4') = k1_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_75,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4') = k1_funct_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_68])).

tff(c_14,plain,(
    ~ r2_hidden(k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4'),k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_79,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_91,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_79])).

tff(c_97,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_91])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_102,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_105,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_105])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ! [B_33,A_34] :
      ( ~ r1_tarski(B_33,A_34)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_34,B_33) ) ),
    inference(resolution,[status(thm)],[c_30,c_8])).

tff(c_43,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_45,plain,(
    ! [A_35] : ~ m1_subset_1(A_35,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_50,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_111,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_51])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.82/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.82/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.82/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.19  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 1.82/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.19  
% 1.99/1.21  tff(f_86, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 1.99/1.21  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.99/1.21  tff(f_66, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 1.99/1.21  tff(f_54, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 1.99/1.21  tff(f_30, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.99/1.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.99/1.21  tff(f_41, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.99/1.21  tff(c_24, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_26, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_22, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.21  tff(c_20, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_18, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_16, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_88, plain, (![D_42, C_43, A_44, B_45]: (r2_hidden(k1_funct_1(D_42, C_43), k2_relset_1(A_44, B_45, D_42)) | k1_xboole_0=B_45 | ~r2_hidden(C_43, A_44) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_42, A_44, B_45) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.99/1.21  tff(c_52, plain, (![A_36, B_37, C_38, D_39]: (k3_funct_2(A_36, B_37, C_38, D_39)=k1_funct_1(C_38, D_39) | ~m1_subset_1(D_39, A_36) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.21  tff(c_58, plain, (![B_37, C_38]: (k3_funct_2('#skF_2', B_37, C_38, '#skF_4')=k1_funct_1(C_38, '#skF_4') | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_37))) | ~v1_funct_2(C_38, '#skF_2', B_37) | ~v1_funct_1(C_38) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_52])).
% 1.99/1.21  tff(c_65, plain, (![B_40, C_41]: (k3_funct_2('#skF_2', B_40, C_41, '#skF_4')=k1_funct_1(C_41, '#skF_4') | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_40))) | ~v1_funct_2(C_41, '#skF_2', B_40) | ~v1_funct_1(C_41))), inference(negUnitSimplification, [status(thm)], [c_26, c_58])).
% 1.99/1.21  tff(c_68, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4')=k1_funct_1('#skF_5', '#skF_4') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_65])).
% 1.99/1.21  tff(c_75, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4')=k1_funct_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_68])).
% 1.99/1.21  tff(c_14, plain, (~r2_hidden(k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.99/1.21  tff(c_79, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_14])).
% 1.99/1.21  tff(c_91, plain, (k1_xboole_0='#skF_3' | ~r2_hidden('#skF_4', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_79])).
% 1.99/1.21  tff(c_97, plain, (k1_xboole_0='#skF_3' | ~r2_hidden('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_91])).
% 1.99/1.21  tff(c_99, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_97])).
% 1.99/1.21  tff(c_102, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_99])).
% 1.99/1.21  tff(c_105, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_102])).
% 1.99/1.21  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_105])).
% 1.99/1.21  tff(c_108, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_97])).
% 1.99/1.21  tff(c_4, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.99/1.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.21  tff(c_30, plain, (![A_31, B_32]: (r2_hidden(A_31, B_32) | v1_xboole_0(B_32) | ~m1_subset_1(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.21  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.21  tff(c_39, plain, (![B_33, A_34]: (~r1_tarski(B_33, A_34) | v1_xboole_0(B_33) | ~m1_subset_1(A_34, B_33))), inference(resolution, [status(thm)], [c_30, c_8])).
% 1.99/1.21  tff(c_43, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_39])).
% 1.99/1.21  tff(c_45, plain, (![A_35]: (~m1_subset_1(A_35, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_43])).
% 1.99/1.21  tff(c_50, plain, $false, inference(resolution, [status(thm)], [c_4, c_45])).
% 1.99/1.21  tff(c_51, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_43])).
% 1.99/1.21  tff(c_111, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_51])).
% 1.99/1.21  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_111])).
% 1.99/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  Inference rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Ref     : 0
% 1.99/1.21  #Sup     : 15
% 1.99/1.21  #Fact    : 0
% 1.99/1.21  #Define  : 0
% 1.99/1.21  #Split   : 4
% 1.99/1.21  #Chain   : 0
% 1.99/1.21  #Close   : 0
% 1.99/1.21  
% 1.99/1.21  Ordering : KBO
% 1.99/1.21  
% 1.99/1.21  Simplification rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Subsume      : 1
% 1.99/1.21  #Demod        : 11
% 1.99/1.21  #Tautology    : 2
% 1.99/1.21  #SimpNegUnit  : 3
% 1.99/1.21  #BackRed      : 5
% 1.99/1.21  
% 1.99/1.21  #Partial instantiations: 0
% 1.99/1.21  #Strategies tried      : 1
% 1.99/1.21  
% 1.99/1.21  Timing (in seconds)
% 1.99/1.21  ----------------------
% 1.99/1.21  Preprocessing        : 0.30
% 1.99/1.21  Parsing              : 0.16
% 1.99/1.21  CNF conversion       : 0.02
% 1.99/1.21  Main loop            : 0.14
% 1.99/1.21  Inferencing          : 0.05
% 1.99/1.21  Reduction            : 0.05
% 1.99/1.21  Demodulation         : 0.03
% 1.99/1.21  BG Simplification    : 0.01
% 1.99/1.21  Subsumption          : 0.02
% 1.99/1.21  Abstraction          : 0.01
% 1.99/1.21  MUC search           : 0.00
% 1.99/1.21  Cooper               : 0.00
% 1.99/1.21  Total                : 0.47
% 1.99/1.21  Index Insertion      : 0.00
% 1.99/1.21  Index Deletion       : 0.00
% 1.99/1.21  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
