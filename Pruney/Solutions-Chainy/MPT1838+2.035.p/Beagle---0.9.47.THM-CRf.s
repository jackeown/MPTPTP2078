%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 139 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [A_28] :
      ( k6_domain_1(A_28,'#skF_2'(A_28)) = A_28
      | ~ v1_zfmisc_1(A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    ! [A_28] :
      ( m1_subset_1('#skF_2'(A_28),A_28)
      | ~ v1_zfmisc_1(A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_384,plain,(
    ! [A_70,B_71] :
      ( k6_domain_1(A_70,B_71) = k1_tarski(B_71)
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_621,plain,(
    ! [A_89] :
      ( k6_domain_1(A_89,'#skF_2'(A_89)) = k1_tarski('#skF_2'(A_89))
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_36,c_384])).

tff(c_723,plain,(
    ! [A_99] :
      ( k1_tarski('#skF_2'(A_99)) = A_99
      | ~ v1_zfmisc_1(A_99)
      | v1_xboole_0(A_99)
      | ~ v1_zfmisc_1(A_99)
      | v1_xboole_0(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_621])).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tarski(A_49),B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_333,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(k1_tarski(A_67),B_68) = B_68
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_138,c_8])).

tff(c_28,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_390,plain,(
    ! [B_72,A_73] :
      ( k1_xboole_0 != B_72
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_28])).

tff(c_397,plain,(
    ! [A_74] :
      ( k1_xboole_0 != A_74
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_390])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_405,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_397,c_46])).

tff(c_404,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_397,c_44])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_115,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_503,plain,(
    ! [C_81,B_82,A_83] :
      ( k1_xboole_0 = C_81
      | k1_xboole_0 = B_82
      | C_81 = B_82
      | k2_xboole_0(B_82,C_81) != k1_tarski(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_521,plain,(
    ! [A_83] :
      ( k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | '#skF_3' = '#skF_4'
      | k1_tarski(A_83) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_503])).

tff(c_528,plain,(
    ! [A_83] : k1_tarski(A_83) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_405,c_404,c_521])).

tff(c_778,plain,(
    ! [A_101] :
      ( A_101 != '#skF_4'
      | ~ v1_zfmisc_1(A_101)
      | v1_xboole_0(A_101)
      | ~ v1_zfmisc_1(A_101)
      | v1_xboole_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_528])).

tff(c_780,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_778])).

tff(c_783,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_780])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.53  
% 2.73/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.73/1.53  
% 2.73/1.53  %Foreground sorts:
% 2.73/1.53  
% 2.73/1.53  
% 2.73/1.53  %Background operators:
% 2.73/1.53  
% 2.73/1.53  
% 2.73/1.53  %Foreground operators:
% 2.73/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.73/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.73/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.73/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.53  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.73/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.53  
% 2.78/1.54  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.78/1.54  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.78/1.54  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.78/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.78/1.54  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.78/1.54  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.78/1.54  tff(f_68, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.78/1.54  tff(f_65, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.78/1.54  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.54  tff(c_42, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.54  tff(c_34, plain, (![A_28]: (k6_domain_1(A_28, '#skF_2'(A_28))=A_28 | ~v1_zfmisc_1(A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.78/1.54  tff(c_36, plain, (![A_28]: (m1_subset_1('#skF_2'(A_28), A_28) | ~v1_zfmisc_1(A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.78/1.54  tff(c_384, plain, (![A_70, B_71]: (k6_domain_1(A_70, B_71)=k1_tarski(B_71) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.54  tff(c_621, plain, (![A_89]: (k6_domain_1(A_89, '#skF_2'(A_89))=k1_tarski('#skF_2'(A_89)) | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_36, c_384])).
% 2.78/1.54  tff(c_723, plain, (![A_99]: (k1_tarski('#skF_2'(A_99))=A_99 | ~v1_zfmisc_1(A_99) | v1_xboole_0(A_99) | ~v1_zfmisc_1(A_99) | v1_xboole_0(A_99))), inference(superposition, [status(thm), theory('equality')], [c_34, c_621])).
% 2.78/1.54  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.54  tff(c_138, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), B_50) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.54  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.54  tff(c_333, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)=B_68 | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_138, c_8])).
% 2.78/1.54  tff(c_28, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.78/1.54  tff(c_390, plain, (![B_72, A_73]: (k1_xboole_0!=B_72 | ~r2_hidden(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_333, c_28])).
% 2.78/1.54  tff(c_397, plain, (![A_74]: (k1_xboole_0!=A_74 | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_390])).
% 2.78/1.54  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.54  tff(c_405, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_397, c_46])).
% 2.78/1.54  tff(c_404, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_397, c_44])).
% 2.78/1.54  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.54  tff(c_115, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.54  tff(c_119, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.78/1.54  tff(c_503, plain, (![C_81, B_82, A_83]: (k1_xboole_0=C_81 | k1_xboole_0=B_82 | C_81=B_82 | k2_xboole_0(B_82, C_81)!=k1_tarski(A_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.78/1.54  tff(c_521, plain, (![A_83]: (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | '#skF_3'='#skF_4' | k1_tarski(A_83)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_119, c_503])).
% 2.78/1.54  tff(c_528, plain, (![A_83]: (k1_tarski(A_83)!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_405, c_404, c_521])).
% 2.78/1.54  tff(c_778, plain, (![A_101]: (A_101!='#skF_4' | ~v1_zfmisc_1(A_101) | v1_xboole_0(A_101) | ~v1_zfmisc_1(A_101) | v1_xboole_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_723, c_528])).
% 2.78/1.54  tff(c_780, plain, (~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_778])).
% 2.78/1.54  tff(c_783, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_780])).
% 2.78/1.54  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_783])).
% 2.78/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.54  
% 2.78/1.54  Inference rules
% 2.78/1.54  ----------------------
% 2.78/1.54  #Ref     : 1
% 2.78/1.54  #Sup     : 187
% 2.78/1.54  #Fact    : 0
% 2.78/1.54  #Define  : 0
% 2.78/1.54  #Split   : 0
% 2.78/1.54  #Chain   : 0
% 2.78/1.54  #Close   : 0
% 2.78/1.54  
% 2.78/1.54  Ordering : KBO
% 2.78/1.54  
% 2.78/1.54  Simplification rules
% 2.78/1.54  ----------------------
% 2.78/1.54  #Subsume      : 18
% 2.78/1.54  #Demod        : 55
% 2.78/1.54  #Tautology    : 107
% 2.78/1.54  #SimpNegUnit  : 11
% 2.78/1.54  #BackRed      : 3
% 2.78/1.54  
% 2.78/1.54  #Partial instantiations: 0
% 2.78/1.54  #Strategies tried      : 1
% 2.78/1.54  
% 2.78/1.54  Timing (in seconds)
% 2.78/1.54  ----------------------
% 2.78/1.54  Preprocessing        : 0.37
% 2.78/1.54  Parsing              : 0.20
% 2.78/1.54  CNF conversion       : 0.02
% 2.78/1.54  Main loop            : 0.30
% 2.78/1.54  Inferencing          : 0.12
% 2.78/1.54  Reduction            : 0.09
% 2.78/1.54  Demodulation         : 0.06
% 2.78/1.54  BG Simplification    : 0.02
% 2.78/1.54  Subsumption          : 0.04
% 2.78/1.54  Abstraction          : 0.02
% 2.78/1.54  MUC search           : 0.00
% 2.78/1.54  Cooper               : 0.00
% 2.78/1.54  Total                : 0.70
% 2.78/1.54  Index Insertion      : 0.00
% 2.78/1.54  Index Deletion       : 0.00
% 2.78/1.54  Index Matching       : 0.00
% 2.78/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
