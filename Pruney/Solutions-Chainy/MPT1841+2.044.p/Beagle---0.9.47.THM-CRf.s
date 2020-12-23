%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   65 (  97 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 209 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1('#skF_3'(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    ! [A_9] : r1_tarski('#skF_3'(A_9),A_9) ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_140,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(A_50,B_49)
      | ~ v1_zfmisc_1(B_49)
      | v1_xboole_0(B_49)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_145,plain,(
    ! [A_51] :
      ( '#skF_3'(A_51) = A_51
      | ~ v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51)
      | v1_xboole_0('#skF_3'(A_51)) ) ),
    inference(resolution,[status(thm)],[c_61,c_140])).

tff(c_16,plain,(
    ! [A_9] : ~ v1_subset_1('#skF_3'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | v1_subset_1(B_44,A_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0('#skF_3'(A_9))
      | v1_subset_1('#skF_3'(A_9),A_9)
      | v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_115])).

tff(c_130,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0('#skF_3'(A_9))
      | v1_xboole_0(A_9) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_125])).

tff(c_150,plain,(
    ! [A_52] :
      ( '#skF_3'(A_52) = A_52
      | ~ v1_zfmisc_1(A_52)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_145,c_130])).

tff(c_153,plain,
    ( '#skF_3'('#skF_5') = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_156,plain,(
    '#skF_3'('#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_153])).

tff(c_170,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_17] :
      ( k6_domain_1(A_17,'#skF_4'(A_17)) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_17] :
      ( m1_subset_1('#skF_4'(A_17),A_17)
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    ! [A_41,B_42] :
      ( k6_domain_1(A_41,B_42) = k1_tarski(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_229,plain,(
    ! [A_57] :
      ( k6_domain_1(A_57,'#skF_4'(A_57)) = k1_tarski('#skF_4'(A_57))
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_320,plain,(
    ! [A_68] :
      ( k1_tarski('#skF_4'(A_68)) = A_68
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68)
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_229])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_399,plain,(
    ! [C_77,A_78] :
      ( C_77 = '#skF_4'(A_78)
      | ~ r2_hidden(C_77,A_78)
      | ~ v1_zfmisc_1(A_78)
      | v1_xboole_0(A_78)
      | ~ v1_zfmisc_1(A_78)
      | v1_xboole_0(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_2])).

tff(c_421,plain,(
    ! [A_79,B_80] :
      ( A_79 = '#skF_4'(B_80)
      | ~ v1_zfmisc_1(B_80)
      | v1_xboole_0(B_80)
      | ~ m1_subset_1(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_20,c_399])).

tff(c_436,plain,
    ( '#skF_4'('#skF_5') = '#skF_6'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_421])).

tff(c_445,plain,
    ( '#skF_4'('#skF_5') = '#skF_6'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_436])).

tff(c_446,plain,(
    '#skF_4'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_445])).

tff(c_241,plain,(
    ! [A_17] :
      ( k1_tarski('#skF_4'(A_17)) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17)
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_229])).

tff(c_453,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_241])).

tff(c_469,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_453])).

tff(c_470,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_469])).

tff(c_102,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_90])).

tff(c_108,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_102])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_109,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_38])).

tff(c_488,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_109])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.32  
% 2.76/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.32  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.76/1.32  
% 2.76/1.32  %Foreground sorts:
% 2.76/1.32  
% 2.76/1.32  
% 2.76/1.32  %Background operators:
% 2.76/1.32  
% 2.76/1.32  
% 2.76/1.32  %Foreground operators:
% 2.76/1.32  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.76/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.76/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.76/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.76/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.76/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.32  
% 2.76/1.34  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.76/1.34  tff(f_50, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.76/1.34  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.76/1.34  tff(f_90, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.76/1.34  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.76/1.34  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.76/1.34  tff(f_77, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.76/1.34  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.76/1.34  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.76/1.34  tff(c_42, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.34  tff(c_36, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.34  tff(c_18, plain, (![A_9]: (m1_subset_1('#skF_3'(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.34  tff(c_53, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.34  tff(c_61, plain, (![A_9]: (r1_tarski('#skF_3'(A_9), A_9))), inference(resolution, [status(thm)], [c_18, c_53])).
% 2.76/1.34  tff(c_140, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(A_50, B_49) | ~v1_zfmisc_1(B_49) | v1_xboole_0(B_49) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.76/1.34  tff(c_145, plain, (![A_51]: ('#skF_3'(A_51)=A_51 | ~v1_zfmisc_1(A_51) | v1_xboole_0(A_51) | v1_xboole_0('#skF_3'(A_51)))), inference(resolution, [status(thm)], [c_61, c_140])).
% 2.76/1.34  tff(c_16, plain, (![A_9]: (~v1_subset_1('#skF_3'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.34  tff(c_115, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | v1_subset_1(B_44, A_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.34  tff(c_125, plain, (![A_9]: (~v1_xboole_0('#skF_3'(A_9)) | v1_subset_1('#skF_3'(A_9), A_9) | v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_18, c_115])).
% 2.76/1.34  tff(c_130, plain, (![A_9]: (~v1_xboole_0('#skF_3'(A_9)) | v1_xboole_0(A_9))), inference(negUnitSimplification, [status(thm)], [c_16, c_125])).
% 2.76/1.34  tff(c_150, plain, (![A_52]: ('#skF_3'(A_52)=A_52 | ~v1_zfmisc_1(A_52) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_145, c_130])).
% 2.76/1.34  tff(c_153, plain, ('#skF_3'('#skF_5')='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_150])).
% 2.76/1.34  tff(c_156, plain, ('#skF_3'('#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_42, c_153])).
% 2.76/1.34  tff(c_170, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 2.76/1.34  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.34  tff(c_20, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.76/1.34  tff(c_30, plain, (![A_17]: (k6_domain_1(A_17, '#skF_4'(A_17))=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.76/1.34  tff(c_32, plain, (![A_17]: (m1_subset_1('#skF_4'(A_17), A_17) | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.76/1.34  tff(c_90, plain, (![A_41, B_42]: (k6_domain_1(A_41, B_42)=k1_tarski(B_42) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.34  tff(c_229, plain, (![A_57]: (k6_domain_1(A_57, '#skF_4'(A_57))=k1_tarski('#skF_4'(A_57)) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_32, c_90])).
% 2.76/1.34  tff(c_320, plain, (![A_68]: (k1_tarski('#skF_4'(A_68))=A_68 | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_30, c_229])).
% 2.76/1.34  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.34  tff(c_399, plain, (![C_77, A_78]: (C_77='#skF_4'(A_78) | ~r2_hidden(C_77, A_78) | ~v1_zfmisc_1(A_78) | v1_xboole_0(A_78) | ~v1_zfmisc_1(A_78) | v1_xboole_0(A_78))), inference(superposition, [status(thm), theory('equality')], [c_320, c_2])).
% 2.76/1.34  tff(c_421, plain, (![A_79, B_80]: (A_79='#skF_4'(B_80) | ~v1_zfmisc_1(B_80) | v1_xboole_0(B_80) | ~m1_subset_1(A_79, B_80))), inference(resolution, [status(thm)], [c_20, c_399])).
% 2.76/1.34  tff(c_436, plain, ('#skF_4'('#skF_5')='#skF_6' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_421])).
% 2.76/1.34  tff(c_445, plain, ('#skF_4'('#skF_5')='#skF_6' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_436])).
% 2.76/1.34  tff(c_446, plain, ('#skF_4'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_42, c_445])).
% 2.76/1.34  tff(c_241, plain, (![A_17]: (k1_tarski('#skF_4'(A_17))=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17) | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(superposition, [status(thm), theory('equality')], [c_30, c_229])).
% 2.76/1.34  tff(c_453, plain, (k1_tarski('#skF_6')='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_446, c_241])).
% 2.76/1.34  tff(c_469, plain, (k1_tarski('#skF_6')='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_453])).
% 2.76/1.34  tff(c_470, plain, (k1_tarski('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_42, c_469])).
% 2.76/1.34  tff(c_102, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_90])).
% 2.76/1.34  tff(c_108, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_102])).
% 2.76/1.34  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.34  tff(c_109, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_38])).
% 2.76/1.34  tff(c_488, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_109])).
% 2.76/1.34  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_488])).
% 2.76/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.34  
% 2.76/1.34  Inference rules
% 2.76/1.34  ----------------------
% 2.76/1.34  #Ref     : 0
% 2.76/1.34  #Sup     : 92
% 2.76/1.34  #Fact    : 0
% 2.76/1.34  #Define  : 0
% 2.76/1.34  #Split   : 1
% 2.76/1.34  #Chain   : 0
% 2.76/1.34  #Close   : 0
% 2.76/1.34  
% 2.76/1.34  Ordering : KBO
% 2.76/1.34  
% 2.76/1.34  Simplification rules
% 2.76/1.34  ----------------------
% 2.76/1.34  #Subsume      : 9
% 2.76/1.34  #Demod        : 33
% 2.76/1.34  #Tautology    : 40
% 2.76/1.34  #SimpNegUnit  : 16
% 2.76/1.34  #BackRed      : 3
% 2.76/1.34  
% 2.76/1.34  #Partial instantiations: 0
% 2.76/1.34  #Strategies tried      : 1
% 2.76/1.34  
% 2.76/1.34  Timing (in seconds)
% 2.76/1.34  ----------------------
% 2.76/1.34  Preprocessing        : 0.31
% 2.76/1.34  Parsing              : 0.16
% 2.76/1.34  CNF conversion       : 0.02
% 2.76/1.34  Main loop            : 0.27
% 2.76/1.34  Inferencing          : 0.11
% 2.76/1.34  Reduction            : 0.07
% 2.76/1.34  Demodulation         : 0.05
% 2.76/1.34  BG Simplification    : 0.02
% 2.76/1.34  Subsumption          : 0.04
% 2.76/1.34  Abstraction          : 0.02
% 2.76/1.34  MUC search           : 0.00
% 2.76/1.34  Cooper               : 0.00
% 2.76/1.34  Total                : 0.61
% 2.76/1.34  Index Insertion      : 0.00
% 2.76/1.34  Index Deletion       : 0.00
% 2.76/1.34  Index Matching       : 0.00
% 2.76/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
