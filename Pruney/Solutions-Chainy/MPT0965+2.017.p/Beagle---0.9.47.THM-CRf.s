%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 138 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_37,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_47,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_127,plain,(
    ! [B_54,A_55,C_56] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_55,B_54,C_56) = A_55
      | ~ v1_funct_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_51,c_134])).

tff(c_139,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_138])).

tff(c_57,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_relset_1(A_33,B_34,C_35) = k2_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_66,plain,(
    ! [A_36,B_37,C_38] :
      ( m1_subset_1(k2_relset_1(A_36,B_37,C_38),k1_zfmisc_1(B_37))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_66])).

tff(c_86,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_81])).

tff(c_93,plain,(
    ! [B_41,A_42] :
      ( r2_hidden(k1_funct_1(B_41,A_42),k2_relat_1(B_41))
      | ~ r2_hidden(A_42,k1_relat_1(B_41))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [B_57,A_58,A_59] :
      ( r2_hidden(k1_funct_1(B_57,A_58),A_59)
      | ~ m1_subset_1(k2_relat_1(B_57),k1_zfmisc_1(A_59))
      | ~ r2_hidden(A_58,k1_relat_1(B_57))
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_151,plain,(
    ! [A_58] :
      ( r2_hidden(k1_funct_1('#skF_4',A_58),'#skF_2')
      | ~ r2_hidden(A_58,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_149])).

tff(c_155,plain,(
    ! [A_60] :
      ( r2_hidden(k1_funct_1('#skF_4',A_60),'#skF_2')
      | ~ r2_hidden(A_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_36,c_139,c_151])).

tff(c_26,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_160,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_26])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.26  
% 2.14/1.26  %Foreground sorts:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Background operators:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Foreground operators:
% 2.14/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.14/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.14/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.26  
% 2.14/1.27  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.14/1.27  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.27  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.14/1.27  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.14/1.27  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.14/1.27  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.14/1.27  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.14/1.27  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.14/1.27  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.27  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.27  tff(c_37, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.27  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_37])).
% 2.14/1.27  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.27  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.27  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.27  tff(c_47, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.27  tff(c_51, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.14/1.27  tff(c_127, plain, (![B_54, A_55, C_56]: (k1_xboole_0=B_54 | k1_relset_1(A_55, B_54, C_56)=A_55 | ~v1_funct_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.27  tff(c_134, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_127])).
% 2.14/1.27  tff(c_138, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_51, c_134])).
% 2.14/1.27  tff(c_139, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_28, c_138])).
% 2.14/1.27  tff(c_57, plain, (![A_33, B_34, C_35]: (k2_relset_1(A_33, B_34, C_35)=k2_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.27  tff(c_61, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_57])).
% 2.14/1.27  tff(c_66, plain, (![A_36, B_37, C_38]: (m1_subset_1(k2_relset_1(A_36, B_37, C_38), k1_zfmisc_1(B_37)) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.27  tff(c_81, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_66])).
% 2.14/1.27  tff(c_86, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_81])).
% 2.14/1.27  tff(c_93, plain, (![B_41, A_42]: (r2_hidden(k1_funct_1(B_41, A_42), k2_relat_1(B_41)) | ~r2_hidden(A_42, k1_relat_1(B_41)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.27  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.27  tff(c_149, plain, (![B_57, A_58, A_59]: (r2_hidden(k1_funct_1(B_57, A_58), A_59) | ~m1_subset_1(k2_relat_1(B_57), k1_zfmisc_1(A_59)) | ~r2_hidden(A_58, k1_relat_1(B_57)) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_93, c_2])).
% 2.14/1.27  tff(c_151, plain, (![A_58]: (r2_hidden(k1_funct_1('#skF_4', A_58), '#skF_2') | ~r2_hidden(A_58, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_149])).
% 2.14/1.27  tff(c_155, plain, (![A_60]: (r2_hidden(k1_funct_1('#skF_4', A_60), '#skF_2') | ~r2_hidden(A_60, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_36, c_139, c_151])).
% 2.14/1.27  tff(c_26, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.27  tff(c_160, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_155, c_26])).
% 2.14/1.27  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_160])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 28
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 0
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 0
% 2.14/1.27  #Demod        : 10
% 2.14/1.27  #Tautology    : 9
% 2.14/1.27  #SimpNegUnit  : 2
% 2.14/1.27  #BackRed      : 1
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.27  Preprocessing        : 0.32
% 2.14/1.27  Parsing              : 0.18
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.16
% 2.14/1.27  Inferencing          : 0.06
% 2.14/1.27  Reduction            : 0.05
% 2.14/1.27  Demodulation         : 0.03
% 2.14/1.27  BG Simplification    : 0.01
% 2.14/1.27  Subsumption          : 0.03
% 2.14/1.27  Abstraction          : 0.01
% 2.14/1.27  MUC search           : 0.00
% 2.14/1.27  Cooper               : 0.00
% 2.14/1.27  Total                : 0.51
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
