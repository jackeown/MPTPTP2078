%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:17 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 163 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_1'(A_20),A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_230,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_275,plain,(
    ! [A_68] :
      ( k6_domain_1(A_68,'#skF_1'(A_68)) = k1_tarski('#skF_1'(A_68))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_34,c_230])).

tff(c_32,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_1'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_290,plain,(
    ! [A_69] :
      ( k1_tarski('#skF_1'(A_69)) = A_69
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69)
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_32])).

tff(c_36,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_112,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [B_46,A_47] :
      ( ~ r1_xboole_0(B_46,A_47)
      | ~ r1_tarski(B_46,A_47)
      | v1_xboole_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_187,plain,(
    ! [A_51,B_52] :
      ( ~ r1_tarski(A_51,B_52)
      | v1_xboole_0(A_51)
      | k4_xboole_0(A_51,B_52) != A_51 ) ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_196,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_187])).

tff(c_201,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_196])).

tff(c_202,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_201])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_193,plain,(
    ! [B_2] :
      ( v1_xboole_0(B_2)
      | k4_xboole_0(B_2,B_2) != B_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_204,plain,(
    ! [B_53] :
      ( v1_xboole_0(B_53)
      | k1_xboole_0 != B_53 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_193])).

tff(c_211,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_204,c_42])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_72])).

tff(c_256,plain,(
    ! [C_62,B_63,A_64] :
      ( k1_xboole_0 = C_62
      | k1_xboole_0 = B_63
      | C_62 = B_63
      | k2_xboole_0(B_63,C_62) != k1_tarski(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_259,plain,(
    ! [A_64] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_64) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_256])).

tff(c_266,plain,(
    ! [A_64] : k1_tarski(A_64) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_202,c_211,c_259])).

tff(c_308,plain,(
    ! [A_70] :
      ( A_70 != '#skF_3'
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70)
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_266])).

tff(c_310,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_308])).

tff(c_313,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_310])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.23  
% 2.25/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.23  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.25/1.23  
% 2.25/1.23  %Foreground sorts:
% 2.25/1.23  
% 2.25/1.23  
% 2.25/1.23  %Background operators:
% 2.25/1.23  
% 2.25/1.23  
% 2.25/1.23  %Foreground operators:
% 2.25/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.25/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.25/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.23  
% 2.36/1.24  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.36/1.24  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.36/1.24  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.36/1.24  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.36/1.24  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.36/1.24  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.36/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.24  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.36/1.24  tff(f_67, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.36/1.24  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.24  tff(c_40, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.24  tff(c_34, plain, (![A_20]: (m1_subset_1('#skF_1'(A_20), A_20) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.36/1.24  tff(c_230, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.24  tff(c_275, plain, (![A_68]: (k6_domain_1(A_68, '#skF_1'(A_68))=k1_tarski('#skF_1'(A_68)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_34, c_230])).
% 2.36/1.24  tff(c_32, plain, (![A_20]: (k6_domain_1(A_20, '#skF_1'(A_20))=A_20 | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.36/1.24  tff(c_290, plain, (![A_69]: (k1_tarski('#skF_1'(A_69))=A_69 | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69) | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69))), inference(superposition, [status(thm), theory('equality')], [c_275, c_32])).
% 2.36/1.24  tff(c_36, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.24  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.24  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.24  tff(c_112, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.24  tff(c_124, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_112])).
% 2.36/1.24  tff(c_20, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.24  tff(c_162, plain, (![B_46, A_47]: (~r1_xboole_0(B_46, A_47) | ~r1_tarski(B_46, A_47) | v1_xboole_0(B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.24  tff(c_187, plain, (![A_51, B_52]: (~r1_tarski(A_51, B_52) | v1_xboole_0(A_51) | k4_xboole_0(A_51, B_52)!=A_51)), inference(resolution, [status(thm)], [c_20, c_162])).
% 2.36/1.24  tff(c_196, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_38, c_187])).
% 2.36/1.24  tff(c_201, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_196])).
% 2.36/1.24  tff(c_202, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_201])).
% 2.36/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.24  tff(c_123, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_112])).
% 2.36/1.24  tff(c_193, plain, (![B_2]: (v1_xboole_0(B_2) | k4_xboole_0(B_2, B_2)!=B_2)), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.36/1.24  tff(c_204, plain, (![B_53]: (v1_xboole_0(B_53) | k1_xboole_0!=B_53)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_193])).
% 2.36/1.24  tff(c_211, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_204, c_42])).
% 2.36/1.24  tff(c_72, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.24  tff(c_84, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_38, c_72])).
% 2.36/1.24  tff(c_256, plain, (![C_62, B_63, A_64]: (k1_xboole_0=C_62 | k1_xboole_0=B_63 | C_62=B_63 | k2_xboole_0(B_63, C_62)!=k1_tarski(A_64))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.36/1.24  tff(c_259, plain, (![A_64]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_64)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_256])).
% 2.36/1.24  tff(c_266, plain, (![A_64]: (k1_tarski(A_64)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_202, c_211, c_259])).
% 2.36/1.24  tff(c_308, plain, (![A_70]: (A_70!='#skF_3' | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_290, c_266])).
% 2.36/1.24  tff(c_310, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_308])).
% 2.36/1.24  tff(c_313, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_310])).
% 2.36/1.24  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_313])).
% 2.36/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.24  
% 2.36/1.24  Inference rules
% 2.36/1.24  ----------------------
% 2.36/1.24  #Ref     : 0
% 2.36/1.24  #Sup     : 60
% 2.36/1.24  #Fact    : 0
% 2.36/1.24  #Define  : 0
% 2.36/1.24  #Split   : 0
% 2.36/1.24  #Chain   : 0
% 2.36/1.24  #Close   : 0
% 2.36/1.24  
% 2.36/1.24  Ordering : KBO
% 2.36/1.24  
% 2.36/1.24  Simplification rules
% 2.36/1.24  ----------------------
% 2.36/1.24  #Subsume      : 7
% 2.36/1.24  #Demod        : 11
% 2.36/1.24  #Tautology    : 31
% 2.36/1.24  #SimpNegUnit  : 7
% 2.36/1.24  #BackRed      : 0
% 2.36/1.24  
% 2.36/1.24  #Partial instantiations: 0
% 2.36/1.24  #Strategies tried      : 1
% 2.36/1.24  
% 2.36/1.24  Timing (in seconds)
% 2.36/1.24  ----------------------
% 2.36/1.24  Preprocessing        : 0.30
% 2.36/1.24  Parsing              : 0.16
% 2.36/1.24  CNF conversion       : 0.02
% 2.36/1.24  Main loop            : 0.18
% 2.36/1.24  Inferencing          : 0.07
% 2.36/1.24  Reduction            : 0.06
% 2.36/1.24  Demodulation         : 0.04
% 2.36/1.24  BG Simplification    : 0.01
% 2.36/1.24  Subsumption          : 0.03
% 2.36/1.24  Abstraction          : 0.01
% 2.36/1.24  MUC search           : 0.00
% 2.36/1.24  Cooper               : 0.00
% 2.36/1.24  Total                : 0.52
% 2.36/1.25  Index Insertion      : 0.00
% 2.36/1.25  Index Deletion       : 0.00
% 2.36/1.25  Index Matching       : 0.00
% 2.36/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
