%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 235 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 604 expanded)
%              Number of equality atoms :   22 ( 229 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_143,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_partfun1(C_31,A_32)
      | ~ v1_funct_2(C_31,A_32,B_33)
      | ~ v1_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_160,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_152])).

tff(c_161,plain,(
    v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_160])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_165,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_161,c_8])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_165])).

tff(c_171,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_170,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_177,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_170])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_172,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_6])).

tff(c_188,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_172])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_189,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_171,c_14])).

tff(c_221,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_177,c_36])).

tff(c_249,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_255,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_221,c_249])).

tff(c_276,plain,(
    ! [A_49] : ~ r2_hidden(A_49,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_255])).

tff(c_281,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_276])).

tff(c_197,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_285,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_281,c_197])).

tff(c_183,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_26])).

tff(c_293,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_183])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_204,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_171,c_12])).

tff(c_227,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_231,plain,(
    m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_227])).

tff(c_251,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_45,k6_partfun1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_231,c_249])).

tff(c_258,plain,(
    ! [A_45] : ~ r2_hidden(A_45,k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_251])).

tff(c_311,plain,(
    ! [A_50] : ~ r2_hidden(A_50,k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_258])).

tff(c_316,plain,(
    v1_xboole_0(k6_partfun1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_311])).

tff(c_323,plain,(
    ! [A_53] :
      ( A_53 = '#skF_4'
      | ~ v1_xboole_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_197])).

tff(c_330,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_316,c_323])).

tff(c_22,plain,(
    ! [A_15] : v1_partfun1(k6_partfun1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_342,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_22])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.06/1.22  
% 2.06/1.22  %Foreground sorts:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Background operators:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Foreground operators:
% 2.06/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.06/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.22  
% 2.06/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.23  tff(f_85, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.06/1.23  tff(f_63, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.06/1.23  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.06/1.23  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.23  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.06/1.24  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.06/1.24  tff(f_67, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.06/1.24  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.24  tff(c_28, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.06/1.24  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_28])).
% 2.06/1.24  tff(c_26, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.06/1.24  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.06/1.24  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.06/1.24  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.06/1.24  tff(c_143, plain, (![C_31, A_32, B_33]: (v1_partfun1(C_31, A_32) | ~v1_funct_2(C_31, A_32, B_33) | ~v1_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.24  tff(c_152, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.06/1.24  tff(c_160, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_152])).
% 2.06/1.24  tff(c_161, plain, (v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_160])).
% 2.06/1.24  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.24  tff(c_165, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_161, c_8])).
% 2.06/1.24  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_165])).
% 2.06/1.24  tff(c_171, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.06/1.24  tff(c_170, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.06/1.24  tff(c_177, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_170])).
% 2.06/1.24  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.24  tff(c_172, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_6])).
% 2.06/1.24  tff(c_188, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_172])).
% 2.06/1.24  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.24  tff(c_189, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_171, c_14])).
% 2.06/1.24  tff(c_221, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_177, c_36])).
% 2.06/1.24  tff(c_249, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.24  tff(c_255, plain, (![A_45]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_45, '#skF_4'))), inference(resolution, [status(thm)], [c_221, c_249])).
% 2.06/1.24  tff(c_276, plain, (![A_49]: (~r2_hidden(A_49, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_255])).
% 2.06/1.24  tff(c_281, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_276])).
% 2.06/1.24  tff(c_197, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_8])).
% 2.06/1.24  tff(c_285, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_281, c_197])).
% 2.06/1.24  tff(c_183, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_26])).
% 2.06/1.24  tff(c_293, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_183])).
% 2.06/1.24  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.24  tff(c_204, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_171, c_12])).
% 2.06/1.24  tff(c_227, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.24  tff(c_231, plain, (m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_227])).
% 2.06/1.24  tff(c_251, plain, (![A_45]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_45, k6_partfun1('#skF_3')))), inference(resolution, [status(thm)], [c_231, c_249])).
% 2.06/1.24  tff(c_258, plain, (![A_45]: (~r2_hidden(A_45, k6_partfun1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_251])).
% 2.06/1.24  tff(c_311, plain, (![A_50]: (~r2_hidden(A_50, k6_partfun1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_258])).
% 2.06/1.24  tff(c_316, plain, (v1_xboole_0(k6_partfun1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_311])).
% 2.06/1.24  tff(c_323, plain, (![A_53]: (A_53='#skF_4' | ~v1_xboole_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_197])).
% 2.06/1.24  tff(c_330, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_316, c_323])).
% 2.06/1.24  tff(c_22, plain, (![A_15]: (v1_partfun1(k6_partfun1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.24  tff(c_342, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_330, c_22])).
% 2.06/1.24  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_342])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 67
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 2
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 2
% 2.06/1.24  #Demod        : 57
% 2.06/1.24  #Tautology    : 49
% 2.06/1.24  #SimpNegUnit  : 3
% 2.06/1.24  #BackRed      : 20
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.28
% 2.06/1.24  Parsing              : 0.15
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.19
% 2.06/1.24  Inferencing          : 0.07
% 2.06/1.24  Reduction            : 0.06
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.01
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.01
% 2.06/1.24  MUC search           : 0.00
% 2.06/1.24  Cooper               : 0.00
% 2.06/1.24  Total                : 0.50
% 2.06/1.24  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
