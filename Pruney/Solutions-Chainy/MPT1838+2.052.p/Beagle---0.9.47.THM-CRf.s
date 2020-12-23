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
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   55 (  95 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 234 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_2'(A_15),A_15)
      | ~ v1_zfmisc_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_122,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(A_46,B_47) = k1_tarski(B_47)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,(
    ! [A_50] :
      ( k6_domain_1(A_50,'#skF_2'(A_50)) = k1_tarski('#skF_2'(A_50))
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_26,c_122])).

tff(c_24,plain,(
    ! [A_15] :
      ( k6_domain_1(A_15,'#skF_2'(A_15)) = A_15
      | ~ v1_zfmisc_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_147,plain,(
    ! [A_51] :
      ( k1_tarski('#skF_2'(A_51)) = A_51
      | ~ v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51)
      | ~ v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_188,plain,(
    ! [A_54,A_55] :
      ( k1_tarski('#skF_2'(A_54)) = A_55
      | k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,A_54)
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54)
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_12])).

tff(c_198,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_188])).

tff(c_207,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_198])).

tff(c_208,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_207])).

tff(c_209,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_1'(A_24,B_25),B_25)
      | r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,'#skF_1'(A_32,B_31))
      | r1_xboole_0(A_32,B_31) ) ),
    inference(resolution,[status(thm)],[c_41,c_18])).

tff(c_59,plain,(
    ! [A_33] : r1_xboole_0(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_34] :
      ( ~ r1_tarski(A_34,k1_xboole_0)
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_59,c_10])).

tff(c_69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_214,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_69])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_214])).

tff(c_220,plain,(
    k1_tarski('#skF_2'('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_138,plain,(
    ! [A_50] :
      ( k1_tarski('#skF_2'(A_50)) = A_50
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50)
      | ~ v1_zfmisc_1(A_50)
      | v1_xboole_0(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_231,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_138])).

tff(c_253,plain,
    ( '#skF_3' = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_231])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_28,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.36/1.30  
% 2.36/1.30  %Foreground sorts:
% 2.36/1.30  
% 2.36/1.30  
% 2.36/1.30  %Background operators:
% 2.36/1.30  
% 2.36/1.30  
% 2.36/1.30  %Foreground operators:
% 2.36/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.36/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.36/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.30  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.36/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.30  
% 2.36/1.31  tff(f_95, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.36/1.31  tff(f_81, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.36/1.31  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.36/1.31  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.36/1.31  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.36/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.36/1.31  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.36/1.31  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.36/1.31  tff(c_34, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.31  tff(c_28, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.31  tff(c_32, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.31  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.31  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.31  tff(c_26, plain, (![A_15]: (m1_subset_1('#skF_2'(A_15), A_15) | ~v1_zfmisc_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.31  tff(c_122, plain, (![A_46, B_47]: (k6_domain_1(A_46, B_47)=k1_tarski(B_47) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.31  tff(c_132, plain, (![A_50]: (k6_domain_1(A_50, '#skF_2'(A_50))=k1_tarski('#skF_2'(A_50)) | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_26, c_122])).
% 2.36/1.31  tff(c_24, plain, (![A_15]: (k6_domain_1(A_15, '#skF_2'(A_15))=A_15 | ~v1_zfmisc_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.31  tff(c_147, plain, (![A_51]: (k1_tarski('#skF_2'(A_51))=A_51 | ~v1_zfmisc_1(A_51) | v1_xboole_0(A_51) | ~v1_zfmisc_1(A_51) | v1_xboole_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 2.36/1.31  tff(c_12, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.31  tff(c_188, plain, (![A_54, A_55]: (k1_tarski('#skF_2'(A_54))=A_55 | k1_xboole_0=A_55 | ~r1_tarski(A_55, A_54) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(superposition, [status(thm), theory('equality')], [c_147, c_12])).
% 2.36/1.31  tff(c_198, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_188])).
% 2.36/1.31  tff(c_207, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_198])).
% 2.36/1.31  tff(c_208, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_34, c_207])).
% 2.36/1.31  tff(c_209, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_208])).
% 2.36/1.31  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.31  tff(c_41, plain, (![A_24, B_25]: (r2_hidden('#skF_1'(A_24, B_25), B_25) | r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.31  tff(c_18, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.36/1.31  tff(c_53, plain, (![B_31, A_32]: (~r1_tarski(B_31, '#skF_1'(A_32, B_31)) | r1_xboole_0(A_32, B_31))), inference(resolution, [status(thm)], [c_41, c_18])).
% 2.36/1.31  tff(c_59, plain, (![A_33]: (r1_xboole_0(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_53])).
% 2.36/1.31  tff(c_10, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.31  tff(c_64, plain, (![A_34]: (~r1_tarski(A_34, k1_xboole_0) | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_59, c_10])).
% 2.36/1.31  tff(c_69, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.36/1.31  tff(c_214, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_69])).
% 2.36/1.31  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_214])).
% 2.36/1.31  tff(c_220, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_208])).
% 2.36/1.31  tff(c_138, plain, (![A_50]: (k1_tarski('#skF_2'(A_50))=A_50 | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50) | ~v1_zfmisc_1(A_50) | v1_xboole_0(A_50))), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 2.36/1.31  tff(c_231, plain, ('#skF_3'='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_220, c_138])).
% 2.36/1.31  tff(c_253, plain, ('#skF_3'='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_231])).
% 2.36/1.31  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_28, c_253])).
% 2.36/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  Inference rules
% 2.36/1.31  ----------------------
% 2.36/1.31  #Ref     : 0
% 2.36/1.31  #Sup     : 45
% 2.36/1.31  #Fact    : 0
% 2.36/1.31  #Define  : 0
% 2.36/1.31  #Split   : 1
% 2.36/1.31  #Chain   : 0
% 2.36/1.31  #Close   : 0
% 2.36/1.31  
% 2.36/1.31  Ordering : KBO
% 2.36/1.31  
% 2.36/1.31  Simplification rules
% 2.36/1.31  ----------------------
% 2.36/1.31  #Subsume      : 5
% 2.36/1.31  #Demod        : 22
% 2.36/1.31  #Tautology    : 18
% 2.36/1.31  #SimpNegUnit  : 5
% 2.36/1.31  #BackRed      : 8
% 2.36/1.31  
% 2.36/1.31  #Partial instantiations: 0
% 2.36/1.31  #Strategies tried      : 1
% 2.36/1.31  
% 2.36/1.31  Timing (in seconds)
% 2.36/1.31  ----------------------
% 2.36/1.32  Preprocessing        : 0.32
% 2.36/1.32  Parsing              : 0.17
% 2.36/1.32  CNF conversion       : 0.02
% 2.36/1.32  Main loop            : 0.19
% 2.36/1.32  Inferencing          : 0.07
% 2.36/1.32  Reduction            : 0.06
% 2.36/1.32  Demodulation         : 0.04
% 2.36/1.32  BG Simplification    : 0.02
% 2.36/1.32  Subsumption          : 0.03
% 2.36/1.32  Abstraction          : 0.01
% 2.36/1.32  MUC search           : 0.00
% 2.36/1.32  Cooper               : 0.00
% 2.36/1.32  Total                : 0.53
% 2.36/1.32  Index Insertion      : 0.00
% 2.36/1.32  Index Deletion       : 0.00
% 2.36/1.32  Index Matching       : 0.00
% 2.36/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
