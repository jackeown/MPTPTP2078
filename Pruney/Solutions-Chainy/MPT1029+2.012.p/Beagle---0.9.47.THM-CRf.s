%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 223 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 584 expanded)
%              Number of equality atoms :   24 ( 229 expanded)
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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_136,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_partfun1(C_27,A_28)
      | ~ v1_funct_2(C_27,A_28,B_29)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_145,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_153,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_145])).

tff(c_154,plain,(
    v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_153])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_158,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_158])).

tff(c_164,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_216,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_6])).

tff(c_163,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_171,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_163])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_166,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_182,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_166])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_190,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_164,c_12])).

tff(c_215,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_171,c_34])).

tff(c_240,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_246,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_40,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_215,c_240])).

tff(c_267,plain,(
    ! [A_44] : ~ r2_hidden(A_44,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_246])).

tff(c_272,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_216,c_267])).

tff(c_177,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_24])).

tff(c_281,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_177])).

tff(c_365,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_1'(A_51),A_51)
      | A_51 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_216])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_199,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_164,c_10])).

tff(c_218,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_222,plain,(
    m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_218])).

tff(c_242,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_40,k6_partfun1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_222,c_240])).

tff(c_249,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_242])).

tff(c_351,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_249])).

tff(c_374,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_365,c_351])).

tff(c_20,plain,(
    ! [A_13] : v1_partfun1(k6_partfun1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_394,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_20])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.12/1.27  
% 2.12/1.27  %Foreground sorts:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Background operators:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Foreground operators:
% 2.12/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.27  
% 2.12/1.29  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.12/1.29  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.12/1.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.12/1.29  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.12/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.29  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.12/1.29  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.12/1.29  tff(f_69, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.12/1.29  tff(c_26, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.29  tff(c_45, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 2.12/1.29  tff(c_24, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.29  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.29  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.29  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.29  tff(c_136, plain, (![C_27, A_28, B_29]: (v1_partfun1(C_27, A_28) | ~v1_funct_2(C_27, A_28, B_29) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.29  tff(c_145, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_136])).
% 2.12/1.29  tff(c_153, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_145])).
% 2.12/1.29  tff(c_154, plain, (v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24, c_153])).
% 2.12/1.29  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.12/1.29  tff(c_158, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_154, c_4])).
% 2.12/1.29  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_158])).
% 2.12/1.29  tff(c_164, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.12/1.29  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.29  tff(c_216, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_6])).
% 2.12/1.29  tff(c_163, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.12/1.29  tff(c_171, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_163])).
% 2.12/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.12/1.29  tff(c_166, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_2])).
% 2.12/1.29  tff(c_182, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_166])).
% 2.12/1.29  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.29  tff(c_190, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_164, c_12])).
% 2.12/1.29  tff(c_215, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_171, c_34])).
% 2.12/1.29  tff(c_240, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.29  tff(c_246, plain, (![A_40]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_40, '#skF_4'))), inference(resolution, [status(thm)], [c_215, c_240])).
% 2.12/1.29  tff(c_267, plain, (![A_44]: (~r2_hidden(A_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_246])).
% 2.12/1.29  tff(c_272, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_216, c_267])).
% 2.12/1.29  tff(c_177, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_24])).
% 2.12/1.29  tff(c_281, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_177])).
% 2.12/1.29  tff(c_365, plain, (![A_51]: (r2_hidden('#skF_1'(A_51), A_51) | A_51='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_216])).
% 2.12/1.29  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.29  tff(c_199, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_164, c_10])).
% 2.12/1.29  tff(c_218, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.29  tff(c_222, plain, (m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_218])).
% 2.12/1.29  tff(c_242, plain, (![A_40]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_40, k6_partfun1('#skF_3')))), inference(resolution, [status(thm)], [c_222, c_240])).
% 2.12/1.29  tff(c_249, plain, (![A_40]: (~r2_hidden(A_40, k6_partfun1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_242])).
% 2.12/1.29  tff(c_351, plain, (![A_40]: (~r2_hidden(A_40, k6_partfun1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_249])).
% 2.12/1.29  tff(c_374, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_365, c_351])).
% 2.12/1.29  tff(c_20, plain, (![A_13]: (v1_partfun1(k6_partfun1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.29  tff(c_394, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_374, c_20])).
% 2.12/1.29  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_394])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 0
% 2.12/1.29  #Sup     : 78
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 2
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 6
% 2.12/1.29  #Demod        : 72
% 2.12/1.29  #Tautology    : 58
% 2.12/1.29  #SimpNegUnit  : 4
% 2.12/1.29  #BackRed      : 21
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.29  Preprocessing        : 0.29
% 2.12/1.29  Parsing              : 0.15
% 2.12/1.29  CNF conversion       : 0.02
% 2.12/1.29  Main loop            : 0.21
% 2.12/1.29  Inferencing          : 0.08
% 2.12/1.29  Reduction            : 0.07
% 2.12/1.29  Demodulation         : 0.05
% 2.12/1.29  BG Simplification    : 0.01
% 2.12/1.29  Subsumption          : 0.03
% 2.12/1.29  Abstraction          : 0.01
% 2.12/1.29  MUC search           : 0.00
% 2.12/1.29  Cooper               : 0.00
% 2.12/1.29  Total                : 0.53
% 2.12/1.29  Index Insertion      : 0.00
% 2.12/1.29  Index Deletion       : 0.00
% 2.12/1.29  Index Matching       : 0.00
% 2.12/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
