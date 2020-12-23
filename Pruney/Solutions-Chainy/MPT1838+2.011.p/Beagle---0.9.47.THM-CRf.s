%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:15 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 139 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    ! [A_26] :
      ( k6_domain_1(A_26,'#skF_3'(A_26)) = A_26
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3'(A_26),A_26)
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_289,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(A_72,B_73) = k1_tarski(B_73)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_610,plain,(
    ! [A_99] :
      ( k6_domain_1(A_99,'#skF_3'(A_99)) = k1_tarski('#skF_3'(A_99))
      | ~ v1_zfmisc_1(A_99)
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_34,c_289])).

tff(c_973,plain,(
    ! [A_130] :
      ( k1_tarski('#skF_3'(A_130)) = A_130
      | ~ v1_zfmisc_1(A_130)
      | v1_xboole_0(A_130)
      | ~ v1_zfmisc_1(A_130)
      | v1_xboole_0(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_610])).

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(k1_tarski(A_67),B_68) = B_68
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_120,c_14])).

tff(c_26,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_259,plain,(
    ! [B_69,A_70] :
      ( k1_xboole_0 != B_69
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_26])).

tff(c_273,plain,(
    ! [A_71] :
      ( k1_xboole_0 != A_71
      | v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_288,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_273,c_44])).

tff(c_287,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_273,c_42])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_111,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_357,plain,(
    ! [C_78,B_79,A_80] :
      ( k1_xboole_0 = C_78
      | k1_xboole_0 = B_79
      | C_78 = B_79
      | k2_xboole_0(B_79,C_78) != k1_tarski(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_369,plain,(
    ! [A_80] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | '#skF_5' = '#skF_4'
      | k1_tarski(A_80) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_357])).

tff(c_378,plain,(
    ! [A_80] : k1_tarski(A_80) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_288,c_287,c_369])).

tff(c_1048,plain,(
    ! [A_131] :
      ( A_131 != '#skF_5'
      | ~ v1_zfmisc_1(A_131)
      | v1_xboole_0(A_131)
      | ~ v1_zfmisc_1(A_131)
      | v1_xboole_0(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_378])).

tff(c_1050,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1048])).

tff(c_1053,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1050])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.43  
% 3.02/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.02/1.43  
% 3.02/1.43  %Foreground sorts:
% 3.02/1.43  
% 3.02/1.43  
% 3.02/1.43  %Background operators:
% 3.02/1.43  
% 3.02/1.43  
% 3.02/1.43  %Foreground operators:
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.02/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.02/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.43  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.02/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.43  
% 3.02/1.44  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.02/1.44  tff(f_84, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.02/1.44  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.02/1.44  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.02/1.44  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.02/1.44  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.02/1.44  tff(f_67, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.02/1.44  tff(f_64, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.02/1.44  tff(c_42, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.02/1.44  tff(c_40, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.02/1.44  tff(c_32, plain, (![A_26]: (k6_domain_1(A_26, '#skF_3'(A_26))=A_26 | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.02/1.44  tff(c_34, plain, (![A_26]: (m1_subset_1('#skF_3'(A_26), A_26) | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.02/1.44  tff(c_289, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.02/1.44  tff(c_610, plain, (![A_99]: (k6_domain_1(A_99, '#skF_3'(A_99))=k1_tarski('#skF_3'(A_99)) | ~v1_zfmisc_1(A_99) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_34, c_289])).
% 3.02/1.44  tff(c_973, plain, (![A_130]: (k1_tarski('#skF_3'(A_130))=A_130 | ~v1_zfmisc_1(A_130) | v1_xboole_0(A_130) | ~v1_zfmisc_1(A_130) | v1_xboole_0(A_130))), inference(superposition, [status(thm), theory('equality')], [c_32, c_610])).
% 3.02/1.44  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.02/1.44  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.44  tff(c_120, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.44  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.02/1.44  tff(c_215, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)=B_68 | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_120, c_14])).
% 3.02/1.44  tff(c_26, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.44  tff(c_259, plain, (![B_69, A_70]: (k1_xboole_0!=B_69 | ~r2_hidden(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_215, c_26])).
% 3.02/1.44  tff(c_273, plain, (![A_71]: (k1_xboole_0!=A_71 | v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_6, c_259])).
% 3.02/1.44  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.02/1.44  tff(c_288, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_273, c_44])).
% 3.02/1.44  tff(c_287, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_273, c_42])).
% 3.02/1.44  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.02/1.44  tff(c_111, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.02/1.44  tff(c_115, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_38, c_111])).
% 3.02/1.44  tff(c_357, plain, (![C_78, B_79, A_80]: (k1_xboole_0=C_78 | k1_xboole_0=B_79 | C_78=B_79 | k2_xboole_0(B_79, C_78)!=k1_tarski(A_80))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.44  tff(c_369, plain, (![A_80]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | '#skF_5'='#skF_4' | k1_tarski(A_80)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_115, c_357])).
% 3.02/1.44  tff(c_378, plain, (![A_80]: (k1_tarski(A_80)!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_288, c_287, c_369])).
% 3.02/1.44  tff(c_1048, plain, (![A_131]: (A_131!='#skF_5' | ~v1_zfmisc_1(A_131) | v1_xboole_0(A_131) | ~v1_zfmisc_1(A_131) | v1_xboole_0(A_131))), inference(superposition, [status(thm), theory('equality')], [c_973, c_378])).
% 3.02/1.44  tff(c_1050, plain, (~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1048])).
% 3.02/1.44  tff(c_1053, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1050])).
% 3.02/1.44  tff(c_1055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1053])).
% 3.02/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.44  
% 3.02/1.44  Inference rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Ref     : 2
% 3.02/1.44  #Sup     : 247
% 3.02/1.44  #Fact    : 0
% 3.02/1.44  #Define  : 0
% 3.02/1.44  #Split   : 0
% 3.02/1.44  #Chain   : 0
% 3.02/1.44  #Close   : 0
% 3.02/1.44  
% 3.02/1.44  Ordering : KBO
% 3.02/1.44  
% 3.02/1.44  Simplification rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Subsume      : 104
% 3.02/1.44  #Demod        : 31
% 3.02/1.44  #Tautology    : 71
% 3.02/1.44  #SimpNegUnit  : 19
% 3.02/1.44  #BackRed      : 0
% 3.02/1.44  
% 3.02/1.44  #Partial instantiations: 0
% 3.02/1.44  #Strategies tried      : 1
% 3.02/1.44  
% 3.02/1.44  Timing (in seconds)
% 3.02/1.44  ----------------------
% 3.02/1.44  Preprocessing        : 0.31
% 3.02/1.44  Parsing              : 0.17
% 3.02/1.44  CNF conversion       : 0.02
% 3.02/1.44  Main loop            : 0.35
% 3.02/1.44  Inferencing          : 0.14
% 3.02/1.44  Reduction            : 0.11
% 3.02/1.44  Demodulation         : 0.07
% 3.02/1.44  BG Simplification    : 0.02
% 3.02/1.45  Subsumption          : 0.06
% 3.02/1.45  Abstraction          : 0.02
% 3.02/1.45  MUC search           : 0.00
% 3.02/1.45  Cooper               : 0.00
% 3.02/1.45  Total                : 0.69
% 3.02/1.45  Index Insertion      : 0.00
% 3.02/1.45  Index Deletion       : 0.00
% 3.02/1.45  Index Matching       : 0.00
% 3.02/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
