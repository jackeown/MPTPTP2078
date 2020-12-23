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
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 110 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 275 expanded)
%              Number of equality atoms :   25 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_2'(A_19),A_19)
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_150,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_189,plain,(
    ! [A_69] :
      ( k6_domain_1(A_69,'#skF_2'(A_69)) = k1_tarski('#skF_2'(A_69))
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_26,plain,(
    ! [A_19] :
      ( k6_domain_1(A_19,'#skF_2'(A_19)) = A_19
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_204,plain,(
    ! [A_70] :
      ( k1_tarski('#skF_2'(A_70)) = A_70
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70)
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_26])).

tff(c_16,plain,(
    ! [B_14] : r1_tarski(k1_tarski(B_14),k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_225,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k1_tarski('#skF_2'(A_71)))
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_16])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_236,plain,(
    ! [A_72,A_73] :
      ( r1_tarski(A_72,k1_tarski('#skF_2'(A_73)))
      | ~ r1_tarski(A_72,A_73)
      | ~ v1_zfmisc_1(A_73)
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(B_14) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_383,plain,(
    ! [A_79,A_80] :
      ( k1_tarski('#skF_2'(A_79)) = A_80
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,A_79)
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_236,c_14])).

tff(c_397,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_383])).

tff(c_408,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_397])).

tff(c_409,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_408])).

tff(c_410,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),A_31)
      | r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_61,plain,(
    ! [A_36,B_37] :
      ( ~ r1_tarski(A_36,'#skF_1'(A_36,B_37))
      | r1_xboole_0(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_49,c_20])).

tff(c_66,plain,(
    ! [B_37] : r1_xboole_0(k1_xboole_0,B_37) ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_160,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r1_tarski(C_63,B_62)
      | ~ r1_tarski(C_63,A_61)
      | v1_xboole_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_167,plain,(
    ! [C_64,B_65] :
      ( ~ r1_tarski(C_64,B_65)
      | ~ r1_tarski(C_64,k1_xboole_0)
      | v1_xboole_0(C_64) ) ),
    inference(resolution,[status(thm)],[c_66,c_160])).

tff(c_171,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_177,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_171])).

tff(c_414,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_177])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_414])).

tff(c_425,plain,(
    k1_tarski('#skF_2'('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_195,plain,(
    ! [A_69] :
      ( k1_tarski('#skF_2'(A_69)) = A_69
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69)
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_26])).

tff(c_442,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_195])).

tff(c_473,plain,
    ( '#skF_3' = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_442])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_30,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.33  
% 2.49/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.34  
% 2.49/1.34  %Foreground sorts:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Background operators:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Foreground operators:
% 2.49/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.49/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.49/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.34  
% 2.49/1.36  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.49/1.36  tff(f_89, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.49/1.36  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.49/1.36  tff(f_67, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.49/1.36  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.49/1.36  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/1.36  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.49/1.36  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.49/1.36  tff(f_61, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.49/1.36  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.36  tff(c_30, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.36  tff(c_34, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.36  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.36  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.36  tff(c_28, plain, (![A_19]: (m1_subset_1('#skF_2'(A_19), A_19) | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.36  tff(c_150, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.36  tff(c_189, plain, (![A_69]: (k6_domain_1(A_69, '#skF_2'(A_69))=k1_tarski('#skF_2'(A_69)) | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.49/1.36  tff(c_26, plain, (![A_19]: (k6_domain_1(A_19, '#skF_2'(A_19))=A_19 | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.36  tff(c_204, plain, (![A_70]: (k1_tarski('#skF_2'(A_70))=A_70 | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_189, c_26])).
% 2.49/1.36  tff(c_16, plain, (![B_14]: (r1_tarski(k1_tarski(B_14), k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.36  tff(c_225, plain, (![A_71]: (r1_tarski(A_71, k1_tarski('#skF_2'(A_71))) | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71))), inference(superposition, [status(thm), theory('equality')], [c_204, c_16])).
% 2.49/1.36  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.49/1.36  tff(c_236, plain, (![A_72, A_73]: (r1_tarski(A_72, k1_tarski('#skF_2'(A_73))) | ~r1_tarski(A_72, A_73) | ~v1_zfmisc_1(A_73) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_225, c_8])).
% 2.49/1.36  tff(c_14, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.36  tff(c_383, plain, (![A_79, A_80]: (k1_tarski('#skF_2'(A_79))=A_80 | k1_xboole_0=A_80 | ~r1_tarski(A_80, A_79) | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_236, c_14])).
% 2.49/1.36  tff(c_397, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_383])).
% 2.49/1.36  tff(c_408, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_397])).
% 2.49/1.36  tff(c_409, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_36, c_408])).
% 2.49/1.36  tff(c_410, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_409])).
% 2.49/1.36  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.36  tff(c_49, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), A_31) | r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.36  tff(c_20, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.36  tff(c_61, plain, (![A_36, B_37]: (~r1_tarski(A_36, '#skF_1'(A_36, B_37)) | r1_xboole_0(A_36, B_37))), inference(resolution, [status(thm)], [c_49, c_20])).
% 2.49/1.36  tff(c_66, plain, (![B_37]: (r1_xboole_0(k1_xboole_0, B_37))), inference(resolution, [status(thm)], [c_10, c_61])).
% 2.49/1.36  tff(c_160, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r1_tarski(C_63, B_62) | ~r1_tarski(C_63, A_61) | v1_xboole_0(C_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.36  tff(c_167, plain, (![C_64, B_65]: (~r1_tarski(C_64, B_65) | ~r1_tarski(C_64, k1_xboole_0) | v1_xboole_0(C_64))), inference(resolution, [status(thm)], [c_66, c_160])).
% 2.49/1.36  tff(c_171, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_167])).
% 2.49/1.36  tff(c_177, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_171])).
% 2.49/1.36  tff(c_414, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_177])).
% 2.49/1.36  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_414])).
% 2.49/1.36  tff(c_425, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_409])).
% 2.49/1.36  tff(c_195, plain, (![A_69]: (k1_tarski('#skF_2'(A_69))=A_69 | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69) | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69))), inference(superposition, [status(thm), theory('equality')], [c_189, c_26])).
% 2.49/1.36  tff(c_442, plain, ('#skF_3'='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_425, c_195])).
% 2.49/1.36  tff(c_473, plain, ('#skF_3'='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_442])).
% 2.49/1.36  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_30, c_473])).
% 2.49/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  Inference rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Ref     : 0
% 2.49/1.36  #Sup     : 91
% 2.49/1.36  #Fact    : 0
% 2.49/1.36  #Define  : 0
% 2.49/1.36  #Split   : 2
% 2.49/1.36  #Chain   : 0
% 2.49/1.36  #Close   : 0
% 2.49/1.36  
% 2.49/1.36  Ordering : KBO
% 2.49/1.36  
% 2.49/1.36  Simplification rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Subsume      : 14
% 2.49/1.36  #Demod        : 43
% 2.49/1.36  #Tautology    : 36
% 2.49/1.36  #SimpNegUnit  : 11
% 2.49/1.36  #BackRed      : 12
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.64/1.36  Preprocessing        : 0.31
% 2.64/1.36  Parsing              : 0.16
% 2.64/1.36  CNF conversion       : 0.02
% 2.64/1.36  Main loop            : 0.28
% 2.64/1.36  Inferencing          : 0.10
% 2.64/1.36  Reduction            : 0.08
% 2.64/1.36  Demodulation         : 0.06
% 2.64/1.36  BG Simplification    : 0.02
% 2.64/1.36  Subsumption          : 0.06
% 2.64/1.36  Abstraction          : 0.01
% 2.64/1.36  MUC search           : 0.00
% 2.64/1.36  Cooper               : 0.00
% 2.64/1.36  Total                : 0.63
% 2.64/1.36  Index Insertion      : 0.00
% 2.64/1.36  Index Deletion       : 0.00
% 2.64/1.36  Index Matching       : 0.00
% 2.64/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
