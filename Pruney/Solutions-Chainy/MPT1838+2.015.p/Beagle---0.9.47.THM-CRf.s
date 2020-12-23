%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:16 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 161 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 418 expanded)
%              Number of equality atoms :   59 ( 184 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_98,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_140,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_36,plain,(
    ! [A_17] :
      ( m1_subset_1('#skF_2'(A_17),A_17)
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_203,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_284,plain,(
    ! [A_51] :
      ( k6_domain_1(A_51,'#skF_2'(A_51)) = k1_tarski('#skF_2'(A_51))
      | ~ v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_34,plain,(
    ! [A_17] :
      ( k6_domain_1(A_17,'#skF_2'(A_17)) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_318,plain,(
    ! [A_55] :
      ( k1_tarski('#skF_2'(A_55)) = A_55
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55)
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_34])).

tff(c_26,plain,(
    ! [B_11,A_10,C_12] :
      ( k1_xboole_0 = B_11
      | k1_tarski(A_10) = B_11
      | k2_xboole_0(B_11,C_12) != k1_tarski(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_377,plain,(
    ! [B_57,A_58,C_59] :
      ( k1_xboole_0 = B_57
      | k1_tarski('#skF_2'(A_58)) = B_57
      | k2_xboole_0(B_57,C_59) != A_58
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58)
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_26])).

tff(c_379,plain,(
    ! [A_58] :
      ( k1_xboole_0 = '#skF_4'
      | k1_tarski('#skF_2'(A_58)) = '#skF_4'
      | A_58 != '#skF_4'
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58)
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_377])).

tff(c_500,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [B_28,A_29] :
      ( ~ r1_tarski(B_28,A_29)
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    ! [A_30] :
      ( ~ r1_tarski(A_30,'#skF_1'(A_30))
      | v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_97,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_510,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_97])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_510])).

tff(c_515,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_521,plain,(
    ! [A_65] :
      ( k1_tarski('#skF_2'(A_65)) = '#skF_4'
      | A_65 != '#skF_4'
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65)
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65) ) ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_107,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_113,plain,(
    ! [A_33] : k2_xboole_0(A_33,k1_xboole_0) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_2])).

tff(c_395,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | k1_tarski('#skF_2'(A_60)) = A_60
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_377])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_208,plain,(
    ! [A_39,C_40,B_41] :
      ( k1_tarski(A_39) = C_40
      | k1_xboole_0 = C_40
      | k2_xboole_0(B_41,C_40) != k1_tarski(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,(
    ! [A_39] :
      ( k1_tarski(A_39) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k1_tarski(A_39) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_208])).

tff(c_228,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_232,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_97])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_232])).

tff(c_236,plain,(
    ! [A_39] :
      ( k1_tarski(A_39) = '#skF_3'
      | k1_tarski(A_39) != '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_416,plain,(
    ! [A_60] :
      ( k1_tarski('#skF_2'(A_60)) = '#skF_3'
      | A_60 != '#skF_4'
      | k1_xboole_0 = A_60
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_236])).

tff(c_527,plain,(
    ! [A_65] :
      ( '#skF_3' = '#skF_4'
      | A_65 != '#skF_4'
      | k1_xboole_0 = A_65
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65)
      | A_65 != '#skF_4'
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65)
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_416])).

tff(c_883,plain,(
    ! [A_72] :
      ( A_72 != '#skF_4'
      | k1_xboole_0 = A_72
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72)
      | A_72 != '#skF_4'
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72)
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_527])).

tff(c_885,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_883])).

tff(c_888,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_885])).

tff(c_890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_515,c_888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.52  
% 2.84/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.84/1.52  
% 2.84/1.52  %Foreground sorts:
% 2.84/1.52  
% 2.84/1.52  
% 2.84/1.52  %Background operators:
% 2.84/1.52  
% 2.84/1.52  
% 2.84/1.52  %Foreground operators:
% 2.84/1.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.84/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.84/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.52  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.84/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.52  
% 3.02/1.53  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.02/1.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.02/1.53  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.02/1.53  tff(f_79, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.02/1.53  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.02/1.53  tff(f_57, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.02/1.53  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.02/1.53  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.02/1.53  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.02/1.53  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.53  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.53  tff(c_98, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.53  tff(c_106, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_98])).
% 3.02/1.53  tff(c_140, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 3.02/1.53  tff(c_36, plain, (![A_17]: (m1_subset_1('#skF_2'(A_17), A_17) | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.02/1.53  tff(c_203, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.02/1.53  tff(c_284, plain, (![A_51]: (k6_domain_1(A_51, '#skF_2'(A_51))=k1_tarski('#skF_2'(A_51)) | ~v1_zfmisc_1(A_51) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_36, c_203])).
% 3.02/1.53  tff(c_34, plain, (![A_17]: (k6_domain_1(A_17, '#skF_2'(A_17))=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.02/1.53  tff(c_318, plain, (![A_55]: (k1_tarski('#skF_2'(A_55))=A_55 | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55) | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55))), inference(superposition, [status(thm), theory('equality')], [c_284, c_34])).
% 3.02/1.53  tff(c_26, plain, (![B_11, A_10, C_12]: (k1_xboole_0=B_11 | k1_tarski(A_10)=B_11 | k2_xboole_0(B_11, C_12)!=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.02/1.53  tff(c_377, plain, (![B_57, A_58, C_59]: (k1_xboole_0=B_57 | k1_tarski('#skF_2'(A_58))=B_57 | k2_xboole_0(B_57, C_59)!=A_58 | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58) | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_318, c_26])).
% 3.02/1.53  tff(c_379, plain, (![A_58]: (k1_xboole_0='#skF_4' | k1_tarski('#skF_2'(A_58))='#skF_4' | A_58!='#skF_4' | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58) | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_140, c_377])).
% 3.02/1.53  tff(c_500, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_379])).
% 3.02/1.53  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.53  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.53  tff(c_87, plain, (![B_28, A_29]: (~r1_tarski(B_28, A_29) | ~r2_hidden(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.02/1.53  tff(c_92, plain, (![A_30]: (~r1_tarski(A_30, '#skF_1'(A_30)) | v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_6, c_87])).
% 3.02/1.53  tff(c_97, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_92])).
% 3.02/1.53  tff(c_510, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_97])).
% 3.02/1.53  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_510])).
% 3.02/1.53  tff(c_515, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_379])).
% 3.02/1.53  tff(c_42, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.53  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.53  tff(c_521, plain, (![A_65]: (k1_tarski('#skF_2'(A_65))='#skF_4' | A_65!='#skF_4' | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65) | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65))), inference(splitRight, [status(thm)], [c_379])).
% 3.02/1.53  tff(c_107, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(resolution, [status(thm)], [c_10, c_98])).
% 3.02/1.53  tff(c_113, plain, (![A_33]: (k2_xboole_0(A_33, k1_xboole_0)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_107, c_2])).
% 3.02/1.53  tff(c_395, plain, (![A_60]: (k1_xboole_0=A_60 | k1_tarski('#skF_2'(A_60))=A_60 | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_113, c_377])).
% 3.02/1.53  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.53  tff(c_208, plain, (![A_39, C_40, B_41]: (k1_tarski(A_39)=C_40 | k1_xboole_0=C_40 | k2_xboole_0(B_41, C_40)!=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.02/1.53  tff(c_211, plain, (![A_39]: (k1_tarski(A_39)='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski(A_39)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_208])).
% 3.02/1.53  tff(c_228, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_211])).
% 3.02/1.53  tff(c_232, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_97])).
% 3.02/1.53  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_232])).
% 3.02/1.53  tff(c_236, plain, (![A_39]: (k1_tarski(A_39)='#skF_3' | k1_tarski(A_39)!='#skF_4')), inference(splitRight, [status(thm)], [c_211])).
% 3.02/1.53  tff(c_416, plain, (![A_60]: (k1_tarski('#skF_2'(A_60))='#skF_3' | A_60!='#skF_4' | k1_xboole_0=A_60 | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_395, c_236])).
% 3.02/1.53  tff(c_527, plain, (![A_65]: ('#skF_3'='#skF_4' | A_65!='#skF_4' | k1_xboole_0=A_65 | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65) | A_65!='#skF_4' | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65) | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65))), inference(superposition, [status(thm), theory('equality')], [c_521, c_416])).
% 3.02/1.53  tff(c_883, plain, (![A_72]: (A_72!='#skF_4' | k1_xboole_0=A_72 | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72) | A_72!='#skF_4' | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72) | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72))), inference(negUnitSimplification, [status(thm)], [c_38, c_527])).
% 3.02/1.53  tff(c_885, plain, (k1_xboole_0='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_883])).
% 3.02/1.53  tff(c_888, plain, (k1_xboole_0='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_885])).
% 3.02/1.53  tff(c_890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_515, c_888])).
% 3.02/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.53  
% 3.02/1.53  Inference rules
% 3.02/1.53  ----------------------
% 3.02/1.53  #Ref     : 3
% 3.02/1.53  #Sup     : 223
% 3.02/1.53  #Fact    : 2
% 3.02/1.53  #Define  : 0
% 3.02/1.53  #Split   : 3
% 3.02/1.53  #Chain   : 0
% 3.02/1.53  #Close   : 0
% 3.02/1.53  
% 3.02/1.53  Ordering : KBO
% 3.02/1.53  
% 3.02/1.53  Simplification rules
% 3.02/1.53  ----------------------
% 3.02/1.53  #Subsume      : 54
% 3.02/1.53  #Demod        : 27
% 3.02/1.53  #Tautology    : 95
% 3.02/1.53  #SimpNegUnit  : 23
% 3.02/1.53  #BackRed      : 15
% 3.02/1.53  
% 3.02/1.53  #Partial instantiations: 0
% 3.02/1.53  #Strategies tried      : 1
% 3.02/1.53  
% 3.02/1.53  Timing (in seconds)
% 3.02/1.53  ----------------------
% 3.02/1.54  Preprocessing        : 0.27
% 3.02/1.54  Parsing              : 0.14
% 3.02/1.54  CNF conversion       : 0.02
% 3.02/1.54  Main loop            : 0.39
% 3.02/1.54  Inferencing          : 0.13
% 3.02/1.54  Reduction            : 0.11
% 3.02/1.54  Demodulation         : 0.08
% 3.02/1.54  BG Simplification    : 0.03
% 3.06/1.54  Subsumption          : 0.10
% 3.06/1.54  Abstraction          : 0.02
% 3.06/1.54  MUC search           : 0.00
% 3.06/1.54  Cooper               : 0.00
% 3.06/1.54  Total                : 0.70
% 3.06/1.54  Index Insertion      : 0.00
% 3.06/1.54  Index Deletion       : 0.00
% 3.06/1.54  Index Matching       : 0.00
% 3.06/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
