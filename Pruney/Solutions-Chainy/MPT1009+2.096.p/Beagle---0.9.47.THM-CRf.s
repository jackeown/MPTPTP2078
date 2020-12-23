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
% DateTime   : Thu Dec  3 10:14:55 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 111 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 231 expanded)
%              Number of equality atoms :   28 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k9_relat_1(B_2,A_1),k2_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    ! [B_27,A_28] :
      ( k1_tarski(k1_funct_1(B_27,A_28)) = k2_relat_1(B_27)
      | k1_tarski(A_28) != k1_relat_1(B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_55,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_61,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_55])).

tff(c_63,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [A_24,B_25,C_26] :
      ( k1_relset_1(A_24,B_25,C_26) = k1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_93,plain,(
    ! [B_43,A_44,C_45] :
      ( k1_xboole_0 = B_43
      | k1_relset_1(A_44,B_43,C_45) = A_44
      | ~ v1_funct_2(C_45,A_44,B_43)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_93])).

tff(c_99,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_96])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_26,c_99])).

tff(c_103,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_106,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_28])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k7_relset_1(A_11,B_12,C_13,D_14) = k9_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_125,plain,(
    ! [D_14] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_14) = k9_relat_1('#skF_4',D_14) ),
    inference(resolution,[status(thm)],[c_106,c_10])).

tff(c_102,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_130,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_102])).

tff(c_131,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_130])).

tff(c_149,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_131])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.97/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.97/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.22  
% 2.12/1.24  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.12/1.24  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.12/1.24  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.12/1.24  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.12/1.24  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.12/1.24  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.12/1.24  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.12/1.24  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_34, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.24  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.12/1.24  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k9_relat_1(B_2, A_1), k2_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.24  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_49, plain, (![B_27, A_28]: (k1_tarski(k1_funct_1(B_27, A_28))=k2_relat_1(B_27) | k1_tarski(A_28)!=k1_relat_1(B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.24  tff(c_24, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_55, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_49, c_24])).
% 2.12/1.24  tff(c_61, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_55])).
% 2.12/1.24  tff(c_63, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_61])).
% 2.12/1.24  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_30, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_40, plain, (![A_24, B_25, C_26]: (k1_relset_1(A_24, B_25, C_26)=k1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.24  tff(c_44, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.12/1.24  tff(c_93, plain, (![B_43, A_44, C_45]: (k1_xboole_0=B_43 | k1_relset_1(A_44, B_43, C_45)=A_44 | ~v1_funct_2(C_45, A_44, B_43) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.24  tff(c_96, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_93])).
% 2.12/1.24  tff(c_99, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_96])).
% 2.12/1.24  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_26, c_99])).
% 2.12/1.24  tff(c_103, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_61])).
% 2.12/1.24  tff(c_106, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_28])).
% 2.12/1.24  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k7_relset_1(A_11, B_12, C_13, D_14)=k9_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.24  tff(c_125, plain, (![D_14]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_14)=k9_relat_1('#skF_4', D_14))), inference(resolution, [status(thm)], [c_106, c_10])).
% 2.12/1.24  tff(c_102, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_61])).
% 2.12/1.24  tff(c_130, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_102])).
% 2.12/1.24  tff(c_131, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_130])).
% 2.12/1.24  tff(c_149, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_131])).
% 2.12/1.24  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_149])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 24
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 1
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 2
% 2.12/1.24  #Demod        : 22
% 2.12/1.24  #Tautology    : 14
% 2.12/1.24  #SimpNegUnit  : 2
% 2.12/1.24  #BackRed      : 6
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.32
% 2.12/1.24  Parsing              : 0.17
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.15
% 2.12/1.24  Inferencing          : 0.05
% 2.12/1.24  Reduction            : 0.05
% 2.12/1.24  Demodulation         : 0.03
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.02
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.50
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
