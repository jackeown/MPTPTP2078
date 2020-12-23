%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 175 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_62,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_54,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [D_10,B_6] : r2_hidden(D_10,k2_tarski(D_10,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_67,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_tarski(A_33)) ),
    inference(resolution,[status(thm)],[c_60,c_67])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_135,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_144,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_135])).

tff(c_149,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_144])).

tff(c_243,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k6_domain_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_252,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_243])).

tff(c_256,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_252])).

tff(c_257,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_256])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_265,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_257,c_34])).

tff(c_304,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(A_70,B_69)
      | ~ v1_zfmisc_1(B_69)
      | v1_xboole_0(B_69)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_310,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_265,c_304])).

tff(c_317,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_310])).

tff(c_318,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_50,c_317])).

tff(c_46,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_150,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_46])).

tff(c_323,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_150])).

tff(c_32,plain,(
    ! [A_17] : m1_subset_1('#skF_4'(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,(
    ! [A_17] : r1_tarski('#skF_4'(A_17),A_17) ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_408,plain,(
    ! [A_78] :
      ( '#skF_4'(A_78) = A_78
      | ~ v1_zfmisc_1(A_78)
      | v1_xboole_0(A_78)
      | v1_xboole_0('#skF_4'(A_78)) ) ),
    inference(resolution,[status(thm)],[c_112,c_304])).

tff(c_30,plain,(
    ! [A_17] : ~ v1_subset_1('#skF_4'(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_274,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | v1_subset_1(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_286,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_4'(A_17))
      | v1_subset_1('#skF_4'(A_17),A_17)
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_32,c_274])).

tff(c_294,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_4'(A_17))
      | v1_xboole_0(A_17) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_286])).

tff(c_413,plain,(
    ! [A_79] :
      ( '#skF_4'(A_79) = A_79
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_408,c_294])).

tff(c_416,plain,
    ( '#skF_4'('#skF_5') = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_413])).

tff(c_419,plain,(
    '#skF_4'('#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_416])).

tff(c_432,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_30])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.37  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.57/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.37  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.57/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.57/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.57/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.37  
% 2.57/1.38  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.57/1.38  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.57/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.57/1.38  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.57/1.38  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.57/1.38  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.57/1.38  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.57/1.38  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.57/1.38  tff(f_62, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.57/1.38  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.57/1.38  tff(c_54, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.38  tff(c_10, plain, (![D_10, B_6]: (r2_hidden(D_10, k2_tarski(D_10, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.38  tff(c_60, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_10])).
% 2.57/1.38  tff(c_67, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.38  tff(c_74, plain, (![A_33]: (~v1_xboole_0(k1_tarski(A_33)))), inference(resolution, [status(thm)], [c_60, c_67])).
% 2.57/1.38  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.57/1.38  tff(c_44, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.57/1.38  tff(c_48, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.57/1.38  tff(c_135, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.38  tff(c_144, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_135])).
% 2.57/1.38  tff(c_149, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_144])).
% 2.57/1.38  tff(c_243, plain, (![A_60, B_61]: (m1_subset_1(k6_domain_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.57/1.38  tff(c_252, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_149, c_243])).
% 2.57/1.38  tff(c_256, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_252])).
% 2.57/1.38  tff(c_257, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_256])).
% 2.57/1.38  tff(c_34, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.57/1.38  tff(c_265, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_257, c_34])).
% 2.57/1.38  tff(c_304, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(A_70, B_69) | ~v1_zfmisc_1(B_69) | v1_xboole_0(B_69) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.57/1.38  tff(c_310, plain, (k1_tarski('#skF_6')='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_265, c_304])).
% 2.57/1.38  tff(c_317, plain, (k1_tarski('#skF_6')='#skF_5' | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_310])).
% 2.57/1.38  tff(c_318, plain, (k1_tarski('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_74, c_50, c_317])).
% 2.57/1.38  tff(c_46, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.57/1.38  tff(c_150, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_46])).
% 2.57/1.38  tff(c_323, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_150])).
% 2.57/1.38  tff(c_32, plain, (![A_17]: (m1_subset_1('#skF_4'(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.38  tff(c_104, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.57/1.38  tff(c_112, plain, (![A_17]: (r1_tarski('#skF_4'(A_17), A_17))), inference(resolution, [status(thm)], [c_32, c_104])).
% 2.57/1.38  tff(c_408, plain, (![A_78]: ('#skF_4'(A_78)=A_78 | ~v1_zfmisc_1(A_78) | v1_xboole_0(A_78) | v1_xboole_0('#skF_4'(A_78)))), inference(resolution, [status(thm)], [c_112, c_304])).
% 2.57/1.38  tff(c_30, plain, (![A_17]: (~v1_subset_1('#skF_4'(A_17), A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.38  tff(c_274, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | v1_subset_1(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.38  tff(c_286, plain, (![A_17]: (~v1_xboole_0('#skF_4'(A_17)) | v1_subset_1('#skF_4'(A_17), A_17) | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_32, c_274])).
% 2.57/1.38  tff(c_294, plain, (![A_17]: (~v1_xboole_0('#skF_4'(A_17)) | v1_xboole_0(A_17))), inference(negUnitSimplification, [status(thm)], [c_30, c_286])).
% 2.57/1.38  tff(c_413, plain, (![A_79]: ('#skF_4'(A_79)=A_79 | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_408, c_294])).
% 2.57/1.38  tff(c_416, plain, ('#skF_4'('#skF_5')='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_413])).
% 2.57/1.38  tff(c_419, plain, ('#skF_4'('#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_50, c_416])).
% 2.57/1.38  tff(c_432, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_419, c_30])).
% 2.57/1.38  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_432])).
% 2.57/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  Inference rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Ref     : 0
% 2.57/1.38  #Sup     : 81
% 2.57/1.38  #Fact    : 2
% 2.57/1.38  #Define  : 0
% 2.57/1.38  #Split   : 1
% 2.57/1.38  #Chain   : 0
% 2.57/1.38  #Close   : 0
% 2.57/1.38  
% 2.57/1.38  Ordering : KBO
% 2.57/1.38  
% 2.57/1.38  Simplification rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Subsume      : 13
% 2.57/1.38  #Demod        : 38
% 2.57/1.38  #Tautology    : 43
% 2.57/1.38  #SimpNegUnit  : 19
% 2.57/1.38  #BackRed      : 5
% 2.57/1.38  
% 2.57/1.38  #Partial instantiations: 0
% 2.57/1.38  #Strategies tried      : 1
% 2.57/1.38  
% 2.57/1.38  Timing (in seconds)
% 2.57/1.38  ----------------------
% 2.57/1.39  Preprocessing        : 0.33
% 2.57/1.39  Parsing              : 0.17
% 2.57/1.39  CNF conversion       : 0.02
% 2.57/1.39  Main loop            : 0.24
% 2.57/1.39  Inferencing          : 0.09
% 2.57/1.39  Reduction            : 0.08
% 2.57/1.39  Demodulation         : 0.06
% 2.57/1.39  BG Simplification    : 0.02
% 2.57/1.39  Subsumption          : 0.04
% 2.57/1.39  Abstraction          : 0.02
% 2.57/1.39  MUC search           : 0.00
% 2.57/1.39  Cooper               : 0.00
% 2.57/1.39  Total                : 0.60
% 2.57/1.39  Index Insertion      : 0.00
% 2.57/1.39  Index Deletion       : 0.00
% 2.57/1.39  Index Matching       : 0.00
% 2.57/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
