%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 108 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 239 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_46,A_47,B_48] :
      ( v4_relat_1(A_46,A_47)
      | ~ r1_tarski(A_46,k2_zfmisc_1(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_82,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_34,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_102,plain,(
    ! [A_51,B_52,C_53] :
      ( v1_finset_1('#skF_1'(A_51,B_52,C_53))
      | ~ r1_tarski(A_51,k2_zfmisc_1(B_52,C_53))
      | ~ v1_finset_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_109,plain,
    ( v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_113,plain,(
    v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(A_32)
      | ~ v1_relat_1(B_33)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_4,c_42])).

tff(c_50,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_230,plain,(
    ! [D_77,B_78,C_79,A_80] :
      ( m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(B_78,C_79)))
      | ~ r1_tarski(k1_relat_1(D_77),B_78)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_80,C_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_303,plain,(
    ! [A_96,B_97,C_98,A_99] :
      ( m1_subset_1(A_96,k1_zfmisc_1(k2_zfmisc_1(B_97,C_98)))
      | ~ r1_tarski(k1_relat_1(A_96),B_97)
      | ~ r1_tarski(A_96,k2_zfmisc_1(A_99,C_98)) ) ),
    inference(resolution,[status(thm)],[c_4,c_230])).

tff(c_322,plain,(
    ! [B_100] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_100,'#skF_5')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_100) ) ),
    inference(resolution,[status(thm)],[c_32,c_303])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_358,plain,(
    ! [B_102] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_102,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_102) ) ),
    inference(resolution,[status(thm)],[c_322,c_2])).

tff(c_366,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_6,'#skF_5'))
      | ~ v4_relat_1('#skF_3',A_6)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_358])).

tff(c_370,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_6,'#skF_5'))
      | ~ v4_relat_1('#skF_3',A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_366])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski('#skF_1'(A_17,B_18,C_19),B_18)
      | ~ r1_tarski(A_17,k2_zfmisc_1(B_18,C_19))
      | ~ v1_finset_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_235,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k2_zfmisc_1('#skF_1'(A_81,B_82,C_83),'#skF_2'(A_81,B_82,C_83)))
      | ~ r1_tarski(A_81,k2_zfmisc_1(B_82,C_83))
      | ~ v1_finset_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_77,plain,(
    ! [A_1,A_44,B_45] :
      ( v4_relat_1(A_1,A_44)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_265,plain,(
    ! [A_81,B_82,C_83] :
      ( v4_relat_1(A_81,'#skF_1'(A_81,B_82,C_83))
      | ~ r1_tarski(A_81,k2_zfmisc_1(B_82,C_83))
      | ~ v1_finset_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_235,c_77])).

tff(c_371,plain,(
    ! [A_103] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_103,'#skF_5'))
      | ~ v4_relat_1('#skF_3',A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_366])).

tff(c_30,plain,(
    ! [D_23] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_23,'#skF_5'))
      | ~ r1_tarski(D_23,'#skF_4')
      | ~ v1_finset_1(D_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_426,plain,(
    ! [A_108] :
      ( ~ r1_tarski(A_108,'#skF_4')
      | ~ v1_finset_1(A_108)
      | ~ v4_relat_1('#skF_3',A_108) ) ),
    inference(resolution,[status(thm)],[c_371,c_30])).

tff(c_430,plain,(
    ! [B_82,C_83] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_82,C_83),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_82,C_83))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_82,C_83))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_265,c_426])).

tff(c_439,plain,(
    ! [B_110,C_111] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_110,C_111),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_110,C_111))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_110,C_111)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_430])).

tff(c_443,plain,(
    ! [C_19] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_19))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_19))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_439])).

tff(c_448,plain,(
    ! [C_113] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_113))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_443])).

tff(c_452,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_448])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_113,c_452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.28/1.31  
% 2.28/1.31  %Foreground sorts:
% 2.28/1.31  
% 2.28/1.31  
% 2.28/1.31  %Background operators:
% 2.28/1.31  
% 2.28/1.31  
% 2.28/1.31  %Foreground operators:
% 2.28/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.28/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.31  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.28/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.31  
% 2.68/1.33  tff(f_87, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 2.68/1.33  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.33  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.68/1.33  tff(f_73, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 2.68/1.33  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.68/1.33  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.68/1.33  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.68/1.33  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.68/1.33  tff(c_32, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.33  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.33  tff(c_72, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.33  tff(c_78, plain, (![A_46, A_47, B_48]: (v4_relat_1(A_46, A_47) | ~r1_tarski(A_46, k2_zfmisc_1(A_47, B_48)))), inference(resolution, [status(thm)], [c_4, c_72])).
% 2.68/1.33  tff(c_82, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_78])).
% 2.68/1.33  tff(c_34, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.33  tff(c_102, plain, (![A_51, B_52, C_53]: (v1_finset_1('#skF_1'(A_51, B_52, C_53)) | ~r1_tarski(A_51, k2_zfmisc_1(B_52, C_53)) | ~v1_finset_1(A_51))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.33  tff(c_109, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_102])).
% 2.68/1.33  tff(c_113, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_109])).
% 2.68/1.33  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.33  tff(c_42, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.33  tff(c_47, plain, (![A_32, B_33]: (v1_relat_1(A_32) | ~v1_relat_1(B_33) | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_4, c_42])).
% 2.68/1.33  tff(c_50, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.68/1.33  tff(c_53, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 2.68/1.33  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.33  tff(c_230, plain, (![D_77, B_78, C_79, A_80]: (m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(B_78, C_79))) | ~r1_tarski(k1_relat_1(D_77), B_78) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_80, C_79))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.33  tff(c_303, plain, (![A_96, B_97, C_98, A_99]: (m1_subset_1(A_96, k1_zfmisc_1(k2_zfmisc_1(B_97, C_98))) | ~r1_tarski(k1_relat_1(A_96), B_97) | ~r1_tarski(A_96, k2_zfmisc_1(A_99, C_98)))), inference(resolution, [status(thm)], [c_4, c_230])).
% 2.68/1.33  tff(c_322, plain, (![B_100]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_100, '#skF_5'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_100))), inference(resolution, [status(thm)], [c_32, c_303])).
% 2.68/1.33  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.33  tff(c_358, plain, (![B_102]: (r1_tarski('#skF_3', k2_zfmisc_1(B_102, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_3'), B_102))), inference(resolution, [status(thm)], [c_322, c_2])).
% 2.68/1.33  tff(c_366, plain, (![A_6]: (r1_tarski('#skF_3', k2_zfmisc_1(A_6, '#skF_5')) | ~v4_relat_1('#skF_3', A_6) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_358])).
% 2.68/1.33  tff(c_370, plain, (![A_6]: (r1_tarski('#skF_3', k2_zfmisc_1(A_6, '#skF_5')) | ~v4_relat_1('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_366])).
% 2.68/1.33  tff(c_26, plain, (![A_17, B_18, C_19]: (r1_tarski('#skF_1'(A_17, B_18, C_19), B_18) | ~r1_tarski(A_17, k2_zfmisc_1(B_18, C_19)) | ~v1_finset_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.33  tff(c_235, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k2_zfmisc_1('#skF_1'(A_81, B_82, C_83), '#skF_2'(A_81, B_82, C_83))) | ~r1_tarski(A_81, k2_zfmisc_1(B_82, C_83)) | ~v1_finset_1(A_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.33  tff(c_77, plain, (![A_1, A_44, B_45]: (v4_relat_1(A_1, A_44) | ~r1_tarski(A_1, k2_zfmisc_1(A_44, B_45)))), inference(resolution, [status(thm)], [c_4, c_72])).
% 2.68/1.33  tff(c_265, plain, (![A_81, B_82, C_83]: (v4_relat_1(A_81, '#skF_1'(A_81, B_82, C_83)) | ~r1_tarski(A_81, k2_zfmisc_1(B_82, C_83)) | ~v1_finset_1(A_81))), inference(resolution, [status(thm)], [c_235, c_77])).
% 2.68/1.33  tff(c_371, plain, (![A_103]: (r1_tarski('#skF_3', k2_zfmisc_1(A_103, '#skF_5')) | ~v4_relat_1('#skF_3', A_103))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_366])).
% 2.68/1.33  tff(c_30, plain, (![D_23]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_23, '#skF_5')) | ~r1_tarski(D_23, '#skF_4') | ~v1_finset_1(D_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.33  tff(c_426, plain, (![A_108]: (~r1_tarski(A_108, '#skF_4') | ~v1_finset_1(A_108) | ~v4_relat_1('#skF_3', A_108))), inference(resolution, [status(thm)], [c_371, c_30])).
% 2.68/1.33  tff(c_430, plain, (![B_82, C_83]: (~r1_tarski('#skF_1'('#skF_3', B_82, C_83), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_82, C_83)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_82, C_83)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_265, c_426])).
% 2.68/1.33  tff(c_439, plain, (![B_110, C_111]: (~r1_tarski('#skF_1'('#skF_3', B_110, C_111), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_110, C_111)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_110, C_111)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_430])).
% 2.68/1.33  tff(c_443, plain, (![C_19]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_19)) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_19)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_439])).
% 2.68/1.33  tff(c_448, plain, (![C_113]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_113)) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_113)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_443])).
% 2.68/1.33  tff(c_452, plain, (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v4_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_370, c_448])).
% 2.68/1.33  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_113, c_452])).
% 2.68/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.33  
% 2.68/1.33  Inference rules
% 2.68/1.33  ----------------------
% 2.68/1.33  #Ref     : 0
% 2.68/1.33  #Sup     : 79
% 2.68/1.33  #Fact    : 0
% 2.68/1.33  #Define  : 0
% 2.68/1.33  #Split   : 3
% 2.68/1.33  #Chain   : 0
% 2.68/1.33  #Close   : 0
% 2.68/1.33  
% 2.68/1.33  Ordering : KBO
% 2.68/1.33  
% 2.68/1.33  Simplification rules
% 2.68/1.33  ----------------------
% 2.68/1.33  #Subsume      : 6
% 2.68/1.33  #Demod        : 27
% 2.68/1.33  #Tautology    : 10
% 2.68/1.33  #SimpNegUnit  : 0
% 2.68/1.33  #BackRed      : 0
% 2.68/1.33  
% 2.68/1.33  #Partial instantiations: 0
% 2.68/1.33  #Strategies tried      : 1
% 2.68/1.33  
% 2.68/1.33  Timing (in seconds)
% 2.68/1.33  ----------------------
% 2.68/1.33  Preprocessing        : 0.28
% 2.68/1.33  Parsing              : 0.16
% 2.68/1.33  CNF conversion       : 0.02
% 2.68/1.33  Main loop            : 0.28
% 2.68/1.33  Inferencing          : 0.12
% 2.68/1.33  Reduction            : 0.07
% 2.68/1.33  Demodulation         : 0.05
% 2.68/1.33  BG Simplification    : 0.01
% 2.68/1.33  Subsumption          : 0.05
% 2.68/1.33  Abstraction          : 0.01
% 2.68/1.33  MUC search           : 0.00
% 2.68/1.33  Cooper               : 0.00
% 2.68/1.33  Total                : 0.59
% 2.68/1.33  Index Insertion      : 0.00
% 2.68/1.33  Index Deletion       : 0.00
% 2.68/1.33  Index Matching       : 0.00
% 2.68/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
