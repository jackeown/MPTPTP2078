%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 103 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 284 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_53,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    m1_subset_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    ! [D_34,C_33,A_31,B_32] :
      ( r2_hidden(k1_funct_1(D_34,C_33),k2_relset_1(A_31,B_32,D_34))
      | k1_xboole_0 = B_32
      | ~ r2_hidden(C_33,A_31)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(D_34,A_31,B_32)
      | ~ v1_funct_1(D_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_401,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k3_funct_2(A_115,B_116,C_117,D_118) = k1_funct_1(C_117,D_118)
      | ~ m1_subset_1(D_118,A_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_2(C_117,A_115,B_116)
      | ~ v1_funct_1(C_117)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_409,plain,(
    ! [B_116,C_117] :
      ( k3_funct_2('#skF_4',B_116,C_117,'#skF_6') = k1_funct_1(C_117,'#skF_6')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_116)))
      | ~ v1_funct_2(C_117,'#skF_4',B_116)
      | ~ v1_funct_1(C_117)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_401])).

tff(c_443,plain,(
    ! [B_128,C_129] :
      ( k3_funct_2('#skF_4',B_128,C_129,'#skF_6') = k1_funct_1(C_129,'#skF_6')
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_128)))
      | ~ v1_funct_2(C_129,'#skF_4',B_128)
      | ~ v1_funct_1(C_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_409])).

tff(c_450,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_7','#skF_6') = k1_funct_1('#skF_7','#skF_6')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_443])).

tff(c_462,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_7','#skF_6') = k1_funct_1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_450])).

tff(c_44,plain,(
    ~ r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_7','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_482,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_44])).

tff(c_489,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_482])).

tff(c_495,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_489])).

tff(c_497,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_500,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_497])).

tff(c_503,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_500])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_503])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_495])).

tff(c_20,plain,(
    ! [A_13] : v1_xboole_0('#skF_3'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [A_13] : '#skF_3'(A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_20])).

tff(c_549,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_77])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.41  
% 2.62/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 2.62/1.41  
% 2.62/1.41  %Foreground sorts:
% 2.62/1.41  
% 2.62/1.41  
% 2.62/1.41  %Background operators:
% 2.62/1.41  
% 2.62/1.41  
% 2.62/1.41  %Foreground operators:
% 2.62/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.41  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.62/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.41  
% 2.62/1.42  tff(f_139, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.62/1.42  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.62/1.42  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.62/1.42  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.62/1.42  tff(f_53, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.62/1.42  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.42  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_52, plain, (m1_subset_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_26, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.62/1.42  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_48, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_42, plain, (![D_34, C_33, A_31, B_32]: (r2_hidden(k1_funct_1(D_34, C_33), k2_relset_1(A_31, B_32, D_34)) | k1_xboole_0=B_32 | ~r2_hidden(C_33, A_31) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(D_34, A_31, B_32) | ~v1_funct_1(D_34))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.62/1.42  tff(c_401, plain, (![A_115, B_116, C_117, D_118]: (k3_funct_2(A_115, B_116, C_117, D_118)=k1_funct_1(C_117, D_118) | ~m1_subset_1(D_118, A_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_2(C_117, A_115, B_116) | ~v1_funct_1(C_117) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.62/1.42  tff(c_409, plain, (![B_116, C_117]: (k3_funct_2('#skF_4', B_116, C_117, '#skF_6')=k1_funct_1(C_117, '#skF_6') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_116))) | ~v1_funct_2(C_117, '#skF_4', B_116) | ~v1_funct_1(C_117) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_401])).
% 2.62/1.42  tff(c_443, plain, (![B_128, C_129]: (k3_funct_2('#skF_4', B_128, C_129, '#skF_6')=k1_funct_1(C_129, '#skF_6') | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_128))) | ~v1_funct_2(C_129, '#skF_4', B_128) | ~v1_funct_1(C_129))), inference(negUnitSimplification, [status(thm)], [c_56, c_409])).
% 2.62/1.42  tff(c_450, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_7', '#skF_6')=k1_funct_1('#skF_7', '#skF_6') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_443])).
% 2.62/1.42  tff(c_462, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_7', '#skF_6')=k1_funct_1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_450])).
% 2.62/1.42  tff(c_44, plain, (~r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_7', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.62/1.42  tff(c_482, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_44])).
% 2.62/1.42  tff(c_489, plain, (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_482])).
% 2.62/1.42  tff(c_495, plain, (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_489])).
% 2.62/1.42  tff(c_497, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_495])).
% 2.62/1.42  tff(c_500, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_497])).
% 2.62/1.42  tff(c_503, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_500])).
% 2.62/1.42  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_503])).
% 2.62/1.42  tff(c_506, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_495])).
% 2.62/1.42  tff(c_20, plain, (![A_13]: (v1_xboole_0('#skF_3'(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.42  tff(c_71, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.42  tff(c_75, plain, (![A_13]: ('#skF_3'(A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_71])).
% 2.62/1.42  tff(c_77, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_20])).
% 2.62/1.42  tff(c_549, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_77])).
% 2.62/1.42  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_549])).
% 2.62/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.42  
% 2.62/1.42  Inference rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Ref     : 0
% 2.62/1.42  #Sup     : 100
% 2.62/1.42  #Fact    : 0
% 2.62/1.42  #Define  : 0
% 2.62/1.42  #Split   : 4
% 2.62/1.42  #Chain   : 0
% 2.62/1.42  #Close   : 0
% 2.62/1.42  
% 2.62/1.42  Ordering : KBO
% 2.62/1.42  
% 2.62/1.42  Simplification rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Subsume      : 33
% 2.62/1.42  #Demod        : 50
% 2.62/1.42  #Tautology    : 36
% 2.62/1.42  #SimpNegUnit  : 19
% 2.62/1.42  #BackRed      : 27
% 2.62/1.42  
% 2.62/1.42  #Partial instantiations: 0
% 2.62/1.42  #Strategies tried      : 1
% 2.62/1.42  
% 2.62/1.42  Timing (in seconds)
% 2.62/1.42  ----------------------
% 2.62/1.43  Preprocessing        : 0.34
% 2.62/1.43  Parsing              : 0.18
% 2.62/1.43  CNF conversion       : 0.03
% 2.62/1.43  Main loop            : 0.31
% 2.62/1.43  Inferencing          : 0.11
% 2.62/1.43  Reduction            : 0.09
% 2.62/1.43  Demodulation         : 0.06
% 2.62/1.43  BG Simplification    : 0.02
% 2.62/1.43  Subsumption          : 0.07
% 2.62/1.43  Abstraction          : 0.02
% 2.62/1.43  MUC search           : 0.00
% 2.62/1.43  Cooper               : 0.00
% 2.62/1.43  Total                : 0.69
% 2.62/1.43  Index Insertion      : 0.00
% 2.62/1.43  Index Deletion       : 0.00
% 2.62/1.43  Index Matching       : 0.00
% 2.62/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
