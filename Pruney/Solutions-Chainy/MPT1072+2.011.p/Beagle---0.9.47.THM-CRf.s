%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 285 expanded)
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

tff(f_89,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_94,plain,(
    ! [D_46,C_47,A_48,B_49] :
      ( r2_hidden(k1_funct_1(D_46,C_47),k2_relset_1(A_48,B_49,D_46))
      | k1_xboole_0 = B_49
      | ~ r2_hidden(C_47,A_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_46,A_48,B_49)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k3_funct_2(A_40,B_41,C_42,D_43) = k1_funct_1(C_42,D_43)
      | ~ m1_subset_1(D_43,A_40)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ v1_funct_1(C_42)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [B_41,C_42] :
      ( k3_funct_2('#skF_2',B_41,C_42,'#skF_4') = k1_funct_1(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_41)))
      | ~ v1_funct_2(C_42,'#skF_2',B_41)
      | ~ v1_funct_1(C_42)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_76,plain,(
    ! [B_44,C_45] :
      ( k3_funct_2('#skF_2',B_44,C_45,'#skF_4') = k1_funct_1(C_45,'#skF_4')
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_44)))
      | ~ v1_funct_2(C_45,'#skF_2',B_44)
      | ~ v1_funct_1(C_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_70])).

tff(c_79,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4') = k1_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_82,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4') = k1_funct_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_79])).

tff(c_16,plain,(
    ~ r2_hidden(k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4'),k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_85,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_97,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_85])).

tff(c_106,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_97])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_112,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_115,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_115])).

tff(c_118,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_34] :
      ( v1_xboole_0(A_34)
      | r2_hidden('#skF_1'(A_34),A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    ! [A_35] :
      ( ~ r1_tarski(A_35,'#skF_1'(A_35))
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_32,c_10])).

tff(c_46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_121,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:47:26 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.98/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.25  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 1.98/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.25  
% 2.02/1.26  tff(f_89, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.02/1.26  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.02/1.26  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.02/1.26  tff(f_57, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.02/1.26  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.02/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.02/1.26  tff(f_44, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.02/1.26  tff(c_26, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_28, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_24, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.26  tff(c_22, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_20, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_18, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_94, plain, (![D_46, C_47, A_48, B_49]: (r2_hidden(k1_funct_1(D_46, C_47), k2_relset_1(A_48, B_49, D_46)) | k1_xboole_0=B_49 | ~r2_hidden(C_47, A_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_46, A_48, B_49) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.26  tff(c_66, plain, (![A_40, B_41, C_42, D_43]: (k3_funct_2(A_40, B_41, C_42, D_43)=k1_funct_1(C_42, D_43) | ~m1_subset_1(D_43, A_40) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(C_42, A_40, B_41) | ~v1_funct_1(C_42) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.26  tff(c_70, plain, (![B_41, C_42]: (k3_funct_2('#skF_2', B_41, C_42, '#skF_4')=k1_funct_1(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_41))) | ~v1_funct_2(C_42, '#skF_2', B_41) | ~v1_funct_1(C_42) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_66])).
% 2.02/1.26  tff(c_76, plain, (![B_44, C_45]: (k3_funct_2('#skF_2', B_44, C_45, '#skF_4')=k1_funct_1(C_45, '#skF_4') | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_44))) | ~v1_funct_2(C_45, '#skF_2', B_44) | ~v1_funct_1(C_45))), inference(negUnitSimplification, [status(thm)], [c_28, c_70])).
% 2.02/1.26  tff(c_79, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4')=k1_funct_1('#skF_5', '#skF_4') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_76])).
% 2.02/1.26  tff(c_82, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4')=k1_funct_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_79])).
% 2.02/1.26  tff(c_16, plain, (~r2_hidden(k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.02/1.26  tff(c_85, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_16])).
% 2.02/1.26  tff(c_97, plain, (k1_xboole_0='#skF_3' | ~r2_hidden('#skF_4', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_85])).
% 2.02/1.26  tff(c_106, plain, (k1_xboole_0='#skF_3' | ~r2_hidden('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_97])).
% 2.02/1.26  tff(c_109, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_106])).
% 2.02/1.26  tff(c_112, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_109])).
% 2.02/1.26  tff(c_115, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_112])).
% 2.02/1.26  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_115])).
% 2.02/1.26  tff(c_118, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_106])).
% 2.02/1.26  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.26  tff(c_32, plain, (![A_34]: (v1_xboole_0(A_34) | r2_hidden('#skF_1'(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.26  tff(c_10, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.26  tff(c_41, plain, (![A_35]: (~r1_tarski(A_35, '#skF_1'(A_35)) | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_32, c_10])).
% 2.02/1.26  tff(c_46, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.02/1.26  tff(c_121, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46])).
% 2.02/1.26  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_121])).
% 2.02/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  Inference rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Ref     : 0
% 2.02/1.26  #Sup     : 17
% 2.02/1.26  #Fact    : 0
% 2.02/1.26  #Define  : 0
% 2.02/1.26  #Split   : 3
% 2.02/1.26  #Chain   : 0
% 2.02/1.26  #Close   : 0
% 2.02/1.26  
% 2.02/1.26  Ordering : KBO
% 2.02/1.26  
% 2.02/1.26  Simplification rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Subsume      : 1
% 2.02/1.26  #Demod        : 12
% 2.02/1.26  #Tautology    : 5
% 2.02/1.26  #SimpNegUnit  : 3
% 2.02/1.26  #BackRed      : 5
% 2.02/1.26  
% 2.02/1.26  #Partial instantiations: 0
% 2.02/1.26  #Strategies tried      : 1
% 2.02/1.26  
% 2.02/1.26  Timing (in seconds)
% 2.02/1.26  ----------------------
% 2.02/1.26  Preprocessing        : 0.31
% 2.02/1.26  Parsing              : 0.17
% 2.02/1.26  CNF conversion       : 0.02
% 2.02/1.26  Main loop            : 0.14
% 2.02/1.26  Inferencing          : 0.05
% 2.02/1.26  Reduction            : 0.04
% 2.02/1.26  Demodulation         : 0.03
% 2.02/1.26  BG Simplification    : 0.01
% 2.02/1.26  Subsumption          : 0.02
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.49
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
